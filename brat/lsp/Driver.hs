{-# LANGUAGE OverloadedStrings #-}

import Control.Concurrent.MVar
import Control.Lens hiding (Iso, to)
import Control.Monad.Except
import Control.Monad.IO.Class
import Data.List.NonEmpty (NonEmpty(..))
import Data.Maybe (fromMaybe)
import Data.Text.Utf16.Rope (toText)
import Data.Text (pack, unpack)
import Language.LSP.Server
import Language.LSP.Diagnostics
import Language.LSP.Protocol.Lens hiding (length, publishDiagnostics)
import Language.LSP.Protocol.Message
import Language.LSP.Protocol.Types
import Language.LSP.VFS
import System.FilePath (dropFileName)
import System.Log.Logger

import Brat.Checker.Types (Store(..), TypedHole)
import Brat.Error
import Brat.FC as FC
import Brat.Load
import Brat.LSP.Find
import Brat.LSP.Holes
import Brat.LSP.State
import qualified Brat.Naming as Name
import Brat.Syntax.Common (UserNameMap)

main :: IO Int
main = do
  ps   <- newMVar emptyPS

  runServer $ ServerDefinition
      { defaultConfig = ()
      , configSection = ""
      , parseConfig = \() _ -> Right ()
      , onConfigChange = \() -> pure ()
      , doInitialize = \env _ -> pure (Right env)
      -- Ignore ClientCapabilities argument
      , staticHandlers = \_ -> handlers ps
      , interpretHandler = \env -> Iso (runLspT env) liftIO
      , options = defaultOptions { optTextDocumentSync = Just syncOptions }
      }
 where
  syncOptions :: TextDocumentSyncOptions
  syncOptions = TextDocumentSyncOptions
    { _openClose         = Just True
    , _change            = Just TextDocumentSyncKind_Incremental
    , _willSave          = Just False
    , _willSaveWaitUntil = Just False
    , _save              = Just $ InR $ SaveOptions $ Just False
    }

sendError :: NormalizedUri -> Error -> LspM () ()
sendError fileUri Err{..} =
  let startPos = maybe (Position 0 0)   (conv . FC.start) fc
      endPos   = maybe (Position 0 100) (conv . FC.end) fc
      diags = [Diagnostic
               (Range startPos endPos)
               (Just DiagnosticSeverity_Error)
               Nothing
               Nothing
               (Just "lsp-brat")
               (pack $ show msg)
               Nothing
               Nothing
               Nothing
              ]
  in publishDiagnostics 1 fileUri Nothing (partitionBySource diags)
 where
  conv :: Pos -> Position
  conv p@(Pos l c) = case msg of
                        LexErr _ -> Position (fromIntegral l) (fromIntegral c)
                        _ -> convPos p

convPos :: Pos -> Position
convPos (Pos l c) = Position (fromIntegral (max 0 (l - 1))) (fromIntegral (max 0 (c - 1)))

-- publish 0 error messages (to delete old ones)
allGood :: NormalizedUri -> LspM () ()
allGood fileUri = publishDiagnostics 0 fileUri Nothing (partitionBySource [])

logHoles :: UserNameMap -> [TypedHole] -> NormalizedUri -> LspM () ()
logHoles nm hs fileUri = publishDiagnostics (length hs) fileUri Nothing (partitionBySource (logHole <$> hs))
 where
  logHole :: TypedHole -> Diagnostic
  logHole h = let (FC start end, info) = holeInfo nm h
                  msg = pack info
                  range = Range (convPos start) (convPos end)
              in  Diagnostic
                  range
                  (Just DiagnosticSeverity_Information)
                  Nothing
                  Nothing
                  (Just "lsp-brat")
                  msg
                  Nothing
                  Nothing
                  Nothing

loadVFile state _ msg = do
  let fileUri = msg ^. params
                . textDocument
                . uri
  let fileName = toNormalizedUri fileUri
  file <- getVirtualFile fileName
  let cwd = maybe "" dropFileName (uriToFilePath fileUri)
  case file of
    Just (VirtualFile _version str rope) -> do
      let file = unpack $ toText rope
      liftIO $ debugM "loadVFile" $ "Found file: " ++ show str
      -- N.B. The lsp server will never look for libraries file outside of the
      -- current working directory because of this argument!
      --                                                ||
      --                                                vv
      env <- liftIO . runExceptT $ loadFiles Name.root (cwd :| []) (show fileName) file
      case env of
        Right (_,newDecls,holes,store,_) -> do
          old <- liftIO $ takeMVar state
          liftIO $ putMVar state (updateState (snd <$> newDecls, holes) old)
          allGood fileName
          logHoles (userNames store) holes fileName
        Left (SrcErr _ err) -> allGood fileName *> sendError fileName err
    Nothing -> do
      liftIO $ debugM "loadVFile" $ "Couldn't find " ++ show fileName ++ " in VFS"

handlers :: MVar ProgramState -> Handlers (LspM ())
handlers state = mconcat
  [ notificationHandler SMethod_Initialized $ const (pure ())
  , notificationHandler SMethod_TextDocumentDidOpen (loadVFile state ("TextDocumentDidOpen" :: String))
  , notificationHandler SMethod_TextDocumentDidChange (loadVFile state ("TextDocumentDidChange" :: String))
  , notificationHandler SMethod_TextDocumentDidSave (loadVFile state ("TextDocumentDidSave" :: String))
  -- Do nothing, never cancel!
  , notificationHandler SMethod_CancelRequest (const (pure ()))
  -- TODO: on hover, give some info
  , requestHandler SMethod_TextDocumentHover $ \req responder -> do
      let conv (Position l c) = Pos (fromIntegral $ l + 1) (fromIntegral $ c + 1)
      st <- liftIO $ readMVar state
      liftIO $ debugM "handlers" "TextDocumentHover"
      let HoverParams _ pos _ = req ^. params
          -- Dummy info to respond with
          info = pack . show <$> getInfo st (conv pos)
          msg =  InL . MarkupContent MarkupKind_PlainText $ fromMaybe mempty info
          range = Range pos pos
          rsp = Hover msg (Just range)
      responder (Right (InL rsp))
  ]
