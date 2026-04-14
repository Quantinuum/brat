import Test.Tasty  (testGroup)
import Test.Tasty.Silver.Interactive (defaultMain)

import Test.Arithmetic

main = do
  defaultMain $ testGroup "All" [test_simplify]