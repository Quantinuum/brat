import Test.Tasty  (testGroup)
import Test.Tasty.Silver.Interactive (defaultMain)

import Test.Abstractor
import Test.Checking
import Test.Graph
import Test.Compile.Hugr
import Test.Elaboration
import Test.Failure
import Test.Libs
import Test.Naming
import Test.Parsing
import Test.Search
import Test.Substitution
import Test.Syntax.Let
import Test.TypeArith

import Brat.Checker.Monad
import Brat.Checker.Types (IsSkolem(..))
import Brat.Syntax.Common
import Brat.Syntax.Value
import Brat.QualName
import Brat.Error
import Control.Monad.Freer
import qualified Data.Set as S
import Debug.Trace
import Test.Util
import Test.Tasty.HUnit (testCase)

coroT1 :: Checking ()
coroT1 = do
  name <- req (Fresh "anything")
  let e = InEnd $ In name 0
  req $ Declare e Braty (Left $ Star []) Definable
  mkFork "t1" (req (ELup e) >>= \case
          Just _ -> err $ InternalError "already defined"
          Nothing -> defineEnd "test" e (VCon (PrefixName [] "nil") [])
      )
  mkYield "coroT1" (S.singleton e) >> pure ()
  traceM "Yield continued"
  v <- req $ ELup e
  case v of
    Just _ -> pure ()
    Nothing -> err $ InternalError "not defined"

coroT2 :: Checking ()
coroT2 = do
  name <- req (Fresh "anything")
  let e = InEnd $ In name 0
  req $ Declare e Braty (Left $ Star []) Definable
  v <- do
    mkYield "coroT2" (S.singleton e)
    req $ ELup e
  -- No way to execute this without a 'v'
  mkFork "t2" $ defineEnd "test" e (VCon (PrefixName [] "nil") [])
  err $ InternalError $ case v of
    Nothing -> "ELup performed without waiting for Yield" -- true in next case too
    Just _ -> "ELup returned value before being Defined"


main = do
  failureTests  <- getFailureTests
  checkingTests <- getCheckingTests
  parsingTests <- getParsingTests
  compilationTests <- setupCompilationTests
  graphTests <- getGraphTests
  let coroTests = testGroup "coroutine"
       [testCase "coroT1" $ assertChecking coroT1
       ,testCase "coroT2" $ assertCheckingFail "Typechecking blocked on" coroT2
       ]
  defaultMain $ testGroup "All" [graphTests
                                ,failureTests
                                ,checkingTests
                                ,letTests
                                ,libDirTests
                                ,nameTests
                                ,parsingTests
                                ,searchTests
                                ,elaborationTests
                                ,substitutionTests
                                ,abstractorTests
                                ,compilationTests
                                ,typeArithTests
                                ,coroTests
                                ]
