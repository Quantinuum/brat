module Brat.Load (loadFilename
                 ,loadFiles
                 ,parseFile
                 ,desugarEnv
                 ) where

import Brat.Checker
import Brat.Checker.Helpers (ensureEmpty, next, showMode, wire)
import Brat.Checker.Monad
import Brat.Checker.Types (Store, TypedHole, VEnv, initStore)
import Brat.Elaborator (elabEnv)
import Brat.Error
import Brat.FC hiding (end)
import Brat.Graph (Graph, NodeType(..))
import Brat.Naming
import Brat.Parser
import Brat.Syntax.Common
import Brat.Syntax.Concrete (FEnv)
import Brat.Syntax.Core
import Brat.Syntax.FuncDecl (FunBody(..), FuncDecl(..), Locality(..))
import Brat.Syntax.Raw
import Brat.Syntax.Value
import Brat.QualName
import Util (duplicates,duplicatesWith)
import Hasochism

import Control.Exception (assert)
import Control.Monad (filterM, foldM, forM, forM_, unless)
import Control.Monad.Except
import Control.Monad.Trans.Class (lift)
import Data.Functor ( (<&>), ($>) )
import Data.List (sort)
import Data.List.HT (viewR)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Graph as G
import qualified Data.Map as M
import Data.Traversable (for)
import System.Directory (doesFileExist)
import System.FilePath

import Prelude hiding (last)

-- A Module is a node in the dependency graph
type FlatMod = ((FEnv, String) -- data at the node: declarations, and file contents
               ,Import -- name of this node
               ,[Import]) -- other nodes on which this depends

-- Result of checking/compiling a module
type VMod = (VEnv
            ,[(QualName, VDecl)] -- all symbols from all modules
            ,[TypedHole]          -- for just the last module
            ,Store  -- Ends declared & defined in the module
            ,Graph) -- per function, first elem is name

emptyMod :: VMod
emptyMod = (M.empty, [], [], initStore, (M.empty, []))

-- N.B. This should only be passed local functions
-- If the decl is a function with pattern matching clauses, return the Name of
-- the box that is created for it. For simple `NoLhs` definitions, we return
-- Nothing.
checkDecl :: Prefix -> VDecl -> [(Tgt, BinderType Brat)] -> Checking ()
checkDecl pre (VDecl FuncDecl{..}) to_define = (fnName -!) $ localFC fnLoc $ do
  trackM "\nCheckDecl:"
  unless (fnLocality == Local) $ err $ InternalError "checkDecl called on ext function"
  getFunTy fnSig >>= \case
    -- We must have a row of nouns as the definition
    Nothing -> case fnBody of
      NoLhs body -> do
        (((), ()), ((), rightUnders)) <- let ?my = Braty
                                             ?props = ()
                                         in  check body ((), to_define)
        case rightUnders of
          [] -> pure ()
          _ -> localFC (fcOf body) $
               err $
               TypeMismatch fnName
               (showRow to_define)
               (showRow $ filter ((`notElem` (fst <$> rightUnders)) . fst) to_define)
      Undefined -> error "No body in `checkDecl`"
      ThunkOf _ -> case fnSig of
        Some ro -> err $ ExpectedThunk (showMode Braty) (show ro)
    Just (Some (my :* Flip cty)) -> getClauses fnBody (my, cty) >>= \case
      Right stuff -> do
        box_out :: Src <- case stuff of
          -- checkBody makes an outer box and wires up PatternMatch within.
          -- We'll wire the output of that box into the Id node representing
          -- this function (to_define)
          (Some (Braty :* Flip cty), body) -> let ?my = Braty in checkBody fnName body cty
          (Some (Kerny :* Flip cty), body) -> let ?my = Kerny in checkBody fnName body cty
        case to_define of
          [(thunk_in, _)] -> case my of
            Braty -> wire (box_out, VFun my cty, thunk_in)
            Kerny -> wire (box_out, VFun my cty, thunk_in)
          [] -> err $ ExpectedThunk (showMode my) "No body"
          row -> err $ ExpectedThunk (showMode my) (showRow row)
      Left body -> let ?my = Braty in let ?props = () in check body ((), to_define) $> ()
 where
  getClauses :: FunBody Term Noun
             -> (Modey m, FunTy m Z)
             -> Checking (Either
                          (WC (Term Chk Noun))
                          (Some (Modey :* Flip FunTy Z), FunBody Term UVerb)
                         )
  getClauses (ThunkOf (WC _ verb)) (my, cty) = pure (Right (Some (my :* Flip cty), verb))
  getClauses (NoLhs rhs) _ = pure (Left rhs)
  getClauses Undefined _ = err (InternalError "No body in `checkDecl`")


  getFunTy :: Some (Ro m Z) -> Checking (Maybe (Some (Modey :* Flip FunTy Z)))
  getFunTy (Some (RPr (_, VFun my cty) R0)) = pure $ Just (Some (my :* Flip cty))
  getFunTy (Some R0) = err $ EmptyRow name
  getFunTy _ = pure Nothing

  uname = PrefixName pre fnName
  name = show uname

loadAlias :: TypeAlias -> Checking (QualName, Alias)
loadAlias (TypeAlias fc name args body) = localFC fc $ do
  (_, [(hhungry, Left k)], _, _) <- next "load_alias" Hypo (S0,Some (Zy :* S0)) (REx ("type", Star args) R0) R0
  let abs = WC fc $ foldr ((:||:) . APat . Bind . fst) AEmpty args
  ([v], unders) <- kindCheck [(hhungry, k)] $ Th (WC fc (Lambda (abs, WC fc body) []))
  ensureEmpty "loadAlias unders" unders
  pure (name, (args, v))

withAliases :: [TypeAlias] -> Checking a -> Checking a
withAliases [] m = m
withAliases (a:as) m = loadAlias a >>= \a -> localAlias a $ withAliases as m

loadStmtsWithEnv :: Namespace -> (VEnv, [(QualName, VDecl)], Store) -> (FilePath, Prefix, FEnv, String) -> Either SrcErr VMod
loadStmtsWithEnv ns (venv, oldDecls, oldEndData) (fname, pre, stmts, cts) = addSrcContext fname cts $ do
  -- hacky mess - cleanup!
  (decls, aliases) <- desugarEnv =<< elabEnv stmts
  -- Note the duplicates here works for anything Eq, but is O(n^2).
  -- TODO Since decl names can be ordered/hashed, we could be much faster.
  let (declNames, _) = unzip oldDecls
  let dups = duplicates (declNames ++ map (PrefixName pre . fnName) decls) in unless (null dups) $
    Left $ dumbErr $ NameClash $ show dups
  -- Generate some stuff for each entry:
    --  * A map from names to VDecls (aka an Env)
    --  * Some overs and outs??
  let (globalNS, newRoot) = split "globals" ns
  (entries, (_holes, kcStore, kcGraph)) <- run venv initStore globalNS $
    withAliases aliases $ forM decls $ \d -> localFC (fnLoc d) $ do
      let name = PrefixName pre (fnName d)
      (thing, ins :->> outs, sig, prefix) <- case fnLocality d of
                        Local -> do
                          -- kindCheckAnnotation gives the signature of an Id node,
                          -- hence ins == outs (modulo haskell's knowledge about their scopes)
                          ins :->> outs <- kindCheckAnnotation Braty () (show name) (fnSig d)
                          pure (Id, ins :->> outs, Some ins, "decl")
                        Extern sym -> do
                          (Some outs) <- kindCheckRow Braty (show name) (fnSig d)
                          pure (Prim sym, R0 :->> outs, Some outs, "prim")
      -- In the Extern case, unders will be empty
      (_, unders, overs, _) <- prefix -! next (show name) thing (S0, Some (Zy :* S0)) ins outs
      pure ((name, VDecl d{fnSig=sig}), (unders, overs))
  trackM "finished kind checking"
  -- We used to check there were no holes from that, but for now we do not bother
  -- A list of local functions (read: with bodies) to define with checkDecl
  let to_define = M.fromList [ (name, unders) | ((name, VDecl decl), (unders, _)) <- entries, fnLocality decl == Local ]
  let vdecls = map fst entries
  -- Now generate environment mapping usernames to nodes in the graph
  venv <- pure $ venv <> M.fromList [(name, overs) | ((name, _), (_, overs)) <- entries]
  ((), (holes, newEndData, graph)) <- run venv kcStore newRoot $ withAliases aliases $ do
    remaining <- "check_defs" -! foldM checkDecl' to_define vdecls
    pure $ assert (M.null remaining) () -- all to_defines were defined
  pure (venv, oldDecls <> vdecls, holes, oldEndData <> newEndData, kcGraph <> graph)
 where
  checkDecl' :: M.Map QualName [(Tgt, BinderType Brat)]
             -> (QualName, VDecl)
             -> Checking (M.Map QualName [(Tgt, BinderType Brat)])
  checkDecl' to_define (name, decl) =
    -- Get the decl out of the map, and delete it from things to define
    case M.updateLookupWithKey (\_ _ -> Nothing) name to_define of
      -- If Nothing: We deleted this from the map, so must have checked it already
      (Nothing, remaining) -> pure remaining
      -- Decl defines are the inputs to the Id node which represents a definition
      (Just decl_defines, remaining) -> remaining <$ checkDecl pre decl decl_defines

loadFilename :: Namespace -> [FilePath] -> String -> ExceptT SrcErr IO VMod
loadFilename ns libDirs file = do
  unless (takeExtension file == ".brat") $ fail $ "Filename " ++ file ++ " must end in .brat"
  let (path, fname) = splitFileName $ dropExtension file
  contents <- lift $ readFile file
  loadFiles ns (path :| libDirs) fname contents

-- Does not read the main file, but does read any imported files
loadFiles :: Namespace -> NonEmpty FilePath -> String -> String
         -> ExceptT SrcErr IO VMod
loadFiles ns (cwd :| extraDirs) fname contents = do
  let mainImport = Import { importName = dummyFC (plain fname)
                          , importQualified = True
                          , importAlias = Nothing
                          , importSelection = ImportAll }
  idx_mods <- M.elems <$> depGraph M.empty mainImport contents
  liftEither $ checkNoCycles idx_mods
  let (g, f, _) = G.graphFromEdges (map snd idx_mods)
  let files = G.topSort (G.transposeG g)
  -- Validate imports
  liftEither . addSrcContext fname contents $ forM_ files (validateImports . f)

  let allStmts = getStmts . f <$> files
  -- remove the prefix for the starting file
  allStmts' <- case viewR allStmts of
    -- the original file should be at the end of the allStmts list
    Just (rest, (_, mainPrf, mainStmts, mainCts)) -> do
      unless (mainPrf == [fname]) $
        throwError (SrcErr "" $ dumbErr (InternalError "Top of dependency graph wasn't main file"))
      deps <- for rest $ \(uname,b,c,d) -> findFile uname <&> (,b,c,d)
      let main = (cwd </> fname ++ ".brat", [], mainStmts, mainCts)
      pure (deps ++ [main])
    Nothing -> throwError (SrcErr "" $ dumbErr (InternalError "Empty dependency graph"))
  -- keep (as we fold) and then return only the graphs from the last file in the list
  liftEither $ foldM
    (\(venv, decls, _, defs, _) -> loadStmtsWithEnv ns (venv, decls, defs))
    emptyMod
--     (fname, [], M.empty, contents)
    allStmts'
  where
    -- builds a map from Import to (index in which discovered, module)
    depGraph :: M.Map Import (Int, FlatMod) -- input map to which to add
             -> Import -> String
             -> ExceptT SrcErr IO (M.Map Import (Int, FlatMod))
    depGraph visited imp cts = let name = unWC (importName imp) in
      case M.lookup imp visited of
        Just _ -> pure visited
        Nothing -> do
          (imports, env) <- liftEither $ parseFile (nameToFile cwd name) cts
          let with_mod = M.insert imp (M.size visited,((env, cts), imp, imports)) visited
          foldM visit with_mod imports
     where
      visit :: M.Map Import (Int, FlatMod) -> Import -> ExceptT SrcErr IO (M.Map Import (Int, FlatMod))
      visit visited' imp' = do
        file <- findFile (unWC (importName imp'))
        cts <- lift $ readFile file
        depGraph visited' imp' cts

    getStmts :: ((FEnv, String), Import, [Import]) -> (QualName, Prefix, FEnv, String)
    getStmts (((decls, ts), cts), Import (WC _ pn@(PrefixName ps name)) qual alias sel, _) =
      let prefix = case (qual, alias) of (True, Nothing) -> ps ++ [name]
                                         (False, Nothing) -> []
                                         (_, Just chosenName) -> [unWC chosenName] in
      let p = case sel of ImportAll -> const True
                          ImportPartial ss -> (\d -> fnName d `elem` map unWC ss)
                          ImportHiding ss -> (\d -> fnName d `notElem` map unWC ss) in
      (pn, prefix, (filter p decls, ts), cts)

    -- Check that the names mentioned in the import actually exist and
    -- that aliases are unique
    validateImports :: ((FEnv, String), Import, [Import]) -> Either Error ()
    validateImports (((decls, _), _), Import name _ _ selection, imports) = do
      let names = case selection of ImportAll -> []
                                    ImportHiding ss -> ss
                                    ImportPartial ss -> ss
      forM_ names (\(WC fc s) -> if s `elem` (fnName <$> decls) then pure ()
                         else throwError $ Err (Just fc) (SymbolNotFound s (show name)))
      let aliases = foldr (\i as -> case importAlias i of Just a -> a:as
                                                          Nothing -> as) [] imports
      case duplicatesWith unWC aliases of
        (WC fc dupl:_) -> throwError $ Err (Just fc) (NameClash ("Alias not unique: " ++ show dupl))
        [] -> pure ()

    findFile :: QualName -> ExceptT SrcErr IO String
    findFile uname = let possibleLocations = [nameToFile dir uname | dir <- cwd:extraDirs] in
                       filterM (lift . doesFileExist) possibleLocations >>= \case
      [] -> throwError $ addSrcName (show uname) $ dumbErr (FileNotFound (show uname) possibleLocations)
      (x:_) -> pure x

    nameToFile :: FilePath -> QualName -> String
    nameToFile dir (PrefixName ps file) = dir </> foldr (</>) file ps ++ ".brat"

checkNoCycles :: [(Int, FlatMod)] -> Either SrcErr ()
checkNoCycles mods =
  let idxAndNames = [(i, unWC (importName n), unWC . importName <$> ns)
                    | (i, (_, n, ns)) <- mods]
      justName (_, n, _) = show n
  in case [verts | G.CyclicSCC verts <- G.stronglyConnCompR idxAndNames] of
    [] -> Right ()
    -- Report just the first SCC. Would be great to reduce to a single smallest cycle,
    -- but Data.Graph doesn't offer anything useful (e.g. Dijkstra's algorithm!)
    scc:_ -> Left $ let scc' = map justName (sort scc) -- sort by indices, then discard
                    in addSrcName (head scc') $ dumbErr $ ImportCycle scc'
