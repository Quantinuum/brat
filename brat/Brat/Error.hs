module Brat.Error (ParseError(..)
                  ,LengthConstraintF(..), LengthConstraint
                  ,BracketErrMsg(..)
                  ,ErrorMsg(..)
                  ,Error(..), showError
                  ,SrcErr(..)
                  ,addSrcName, addSrcContext
                  ,eitherIO
                  ,dumbErr
                  ) where

import Brat.FC
import Data.Bracket
import Brat.Syntax.Port (PortName)

import Data.List (intercalate)
import System.Exit

newtype ParseError = PE { pretty :: String }

instance Show ParseError where
  show = pretty

data LengthConstraintF a = Length a | LongerThan a deriving (Eq, Functor)
instance Show a => Show (LengthConstraintF a) where
  show (Length a) = show a
  show (LongerThan a) = "(> " ++ show a ++ ")"

type LengthConstraint = LengthConstraintF Int

data BracketErrMsg
  = EOFInBracket BracketType -- FC in enclosing `Err` should point to the open bracket
  -- FC here is opening; closing FC in the enclosing `Err`
  | OpenCloseMismatch (FC, BracketType) BracketType
  | UnexpectedClose BracketType

instance Show BracketErrMsg where
  show (EOFInBracket b) = "File ended before this " ++ showOpen b ++ " was closed"
  show (OpenCloseMismatch (openFC, bOpen) bClose) = unwords ["This"
                                                            ,showClose bClose
                                                            ,"doesn't match the"
                                                            ,showOpen bOpen
                                                            ,"at"
                                                            ,show openFC
                                                            ]
  show (UnexpectedClose b) = unwords ["There is no"
                                     ,showOpen b
                                     ,"for this"
                                     ,showClose b
                                     ,"to close"
                                     ]

data ErrorMsg
 = TypeErr String
 -- Term, Expected type, Actual type
 | TypeMismatch String String String
 -- Term, Expected kind, Actual kind
 | KindMismatch String String String
 | ExpectedThunk String String
 | PattErr String
 | VarNotFound String
 | KVarNotFound String
 | NothingToBind String
 -- Term, Type, Expected Length, Actual Length
 | VecLength String String String LengthConstraint
 -- Binder, Type, Expected Length, Actual Length
 | VecPatLength String String String LengthConstraint
 -- Term, Type
 | NotVecPat String String

 | EmptyRow String
 | MultipleOutputsForThunk String
 | VecEval String
 | ParseErr ParseError
 | LexErr ParseError
 | ElabErr String
 | DesugarErr String
 | EvalErr String
 | NameClash String
 | MainNotFound
 | BadCons String
 -- function, [argument]
 | Unimplemented String [String]
 | ImportCycle [String]
 | FileNotFound String [String]
 | SymbolNotFound String String
 | InternalError String
 | AmbiguousPortPull PortName String
 | BadPortPull PortName String
 | VConNotFound String
 | TyConNotFound String String
 | MatchingOnTypes
 | ThunkInKernel String
 | InvalidThunkType String
 -- Expected, Actual
 | NumMatchFail String String
 | ValMatchFail String String
 -- Constructor, Type
 | UnrecognisedConstructor String String
 | ArithInKernel
 | ArithNotExpected String
 | UnificationError String
 | UnreachableBranch
 | UnrecognisedTypeCon String
 | WrongModeForType String
 -- For thunks which don't address enough inputs, or produce enough outputs.
 -- The argument is the row of unused connectors
 | ThunkLeftOvers String
 | ThunkLeftUnders String
 | BracketErr BracketErrMsg
 | RemainingNatHopes [String]

instance Show ErrorMsg where
  show (TypeErr x) = "Type error: " ++ x
  show (TypeMismatch tm exp act)
    = unlines ["Type mismatch when checking " ++ tm
              ,"Expected: " ++ exp
              ,"But got:  " ++ act
              ]
  show (KindMismatch tm exp act)
    = unlines ["Kind mismatch when checking " ++ tm
              ,"Expected: " ++ exp
              ,"But got:  " ++ act
              ]

  show (ExpectedThunk m row)
    = unlines ["Expected function to be a " ++ m ++ "thunk, but found:"
              ,"  " ++ row
              ]
  show (NothingToBind x) = "Nothing to bind to: " ++ x
  show (VecLength tm ty exp act) = unlines ["Expected vector of length " ++ exp
                                       ,"from the type:  " ++ ty
                                       ,"but got vector: " ++ tm
                                       ,"of length " ++ show act
                                       ]
  show (VecPatLength abs ty exp act) = unlines ["Pattern: " ++ abs
                                       ,"doesn't match type " ++ ty
                                       ,"(expected vector pattern of length " ++ exp ++
                                        " but got vector pattern of length " ++ show act ++ ")"
                                       ]
  show (NotVecPat tm ty)= unwords ["Expected", tm
                                  ,"to be a vector pattern when binding type", ty]

  show (EmptyRow fn) = "Declaration of " ++ fn ++ " doesn't have any outputs"
  show (MultipleOutputsForThunk fn) = unwords ["Declaration of"
                                              ,fn
                                              ,"has too many outputs:"
                                              ,"expected one thunk type"
                                              ]
  show (VecEval n) = "Couldn't determine that " ++ n ++ " is a Nat"
  show (PattErr x) = "Type error in pattern: " ++ x
  show (ParseErr x) = "Parse error " ++ show x
  show (LexErr x) = "Lex error " ++ show x
  show (ElabErr x) = "Elab error " ++ show x
  show (DesugarErr x) = "Desugar error " ++ x
  show (EvalErr x) = "Eval error " ++ x
  show (NameClash x) = "Name clash: " ++ x
  show (VarNotFound x) = x ++ " not found in (value) environment"
  show (KVarNotFound x) = x ++ " not found in kernel context"
  show MainNotFound = "No function found called \"main\""
  show (BadCons x) = "Expected two arguments to `cons` but got: " ++ x
  show (Unimplemented f args) = unwords ("Unimplemented, sorry! --":f:args)
  show (ImportCycle mods) = unwords ["Cyclic imports: modules all transitively import each other:"
                                    ,intercalate ", " mods]
  show (FileNotFound f dirs) = unlines (("File not found: " ++ show f):"Looked for it at:":dirs)
  show (SymbolNotFound s i) = "Symbol `" ++ s ++ "` not found in `" ++ i ++ "`"
  show (InternalError x) = "Internal error: " ++ x
  show (AmbiguousPortPull p row) = "Port " ++ p ++ " is ambiguous in " ++ row
  show (BadPortPull p row) = "Port not found: " ++ p ++ " in " ++ row
  show (VConNotFound x) = "Value constructor not recognised: " ++ x
  show (TyConNotFound ty v) = show v ++ " is not a valid constructor for type " ++ ty
  show MatchingOnTypes = "Trying to pattern match on a type"
  show (ThunkInKernel tm) = "Thunks not allowed in kernels: " ++ tm
  show (InvalidThunkType ty) = "Invalid thunk type: " ++ ty
  show (NumMatchFail exp act) = unlines ["Failed matching number pattern"
                                        ,"  Expected: " ++ exp
                                        ,"  Got:      " ++ act
                                        ]
  show (ValMatchFail exp act) = unlines ["Failed matching pattern"
                                        ,"  Expected: " ++ exp
                                        ,"  Got:      " ++ act
                                        ]
  show (UnrecognisedConstructor c ty) = unlines ["Unrecognised constructor: " ++ c
                                                ,"For type: " ++ ty
                                                ]
  show (UnrecognisedTypeCon c) = "Unrecognised type constructor: " ++ c
  show (WrongModeForType c) = "Type constructor " ++ show c ++ " isn't valid in this context"
  show ArithInKernel = "Arithmetic expressions not allowed in kernels"
  show (ArithNotExpected tm) = "Expected " ++ tm ++ " but got arithmetic expression"
  -- TODO: Make all of these use existing errors
  show (UnificationError str) = "Unification error: " ++ str
  show UnreachableBranch = "Branch cannot be reached"
  show (ThunkLeftOvers overs) = "Expected function to address all inputs, but " ++ overs ++ " wasn't used"
  show (ThunkLeftUnders unders) = "Expected function to return additional values of type: " ++ unders
  show (BracketErr msg) = show msg
  show (RemainingNatHopes hs) = unlines ("Expected to work out values for these holes:":(("    " ++) <$> hs))

data Error = Err { fc  :: Maybe FC
                 , msg :: ErrorMsg
                 }
-- We could make this just 'instance Show' but this makes the few cases
-- where we show an Error (without filename or contents) explicit.
showError :: Error -> String
showError (Err _ msg) = show msg

instance Show Error where
  show = showError -- TODO: Delete

data SrcErr = SrcErr String Error

instance Show SrcErr where
  show (SrcErr prelim Err{msg=msg}) = unlines [prelim, "  " ++ show msg]

errHeader :: String -> String
errHeader name = "Error in " ++ name ++ ":"

addSrcName :: String -> Error -> SrcErr
addSrcName fname = SrcErr (errHeader fname)

addSrcContext :: String -> String -> Either Error t -> Either SrcErr t
addSrcContext _ _ (Right r) = Right r
addSrcContext fname cts (Left err@Err{fc=fc}) = Left (SrcErr msg err)
 where
  msg = case fc of
    Just fc -> unlines (errHeader (fname ++ prettyFC fc)
                       :showFileContext cts fc
                       )
    Nothing -> errHeader fname

  prettyFC fc = let Pos startLine _ = start fc
                    Pos endLine _ = end fc
                in  if startLine == endLine
                    then " on line " ++ show startLine
                    else " on lines " ++ show startLine ++ "-" ++ show endLine

showFileContext :: String -> FC -> [String]
showFileContext contents fc = let
    -- taking 1 off to convert 1-indexed user line numbers to 0-indexed list indices
    startLineN = line (start fc) - 1
    endLineN = line (end fc) - 1
    startCol = col (start fc) - 1
    endCol = col (end fc) - 1 -- exclusive
    ls = lines contents
  in case endLineN - startLineN of
       0 -> [ls!!startLineN, highlightSection startCol endCol]
       n | n > 0 -> let (first:rest) = drop (startLineN - 1) $ take (endLineN + 1) ls
                        (last:rmid) = reverse rest
                    in [first, highlightSection startCol (length first)]
                       ++ (reverse rmid >>= (\l -> [l, highlightSection 0 (length l)]))
                       ++ [last, highlightSection 0 endCol]
       -- Line numbers are borked
       _ -> []
 where
  highlightSection :: Int -> Int -> String
  highlightSection start end =
    replicate start ' ' ++ replicate (end - start) '^'


eitherIO :: Either SrcErr a -> IO a
eitherIO (Left e) = die (show e)
eitherIO (Right a) = pure a

dumbErr :: ErrorMsg -> Error
dumbErr = Err Nothing
