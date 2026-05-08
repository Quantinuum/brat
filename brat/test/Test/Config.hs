module Test.Config (IgnoreValidation(..)) where

import Data.Tagged (Tagged(..))
import Test.Tasty.Options (IsOption(..), flagCLParser)

data IgnoreValidation = IgnoreValidation Bool
instance IsOption IgnoreValidation where
  defaultValue = IgnoreValidation False
  parseValue s = if s == "ignore-validation" then Just defaultValue else Nothing
  optionName = Tagged "ignore-validation"
  optionHelp = Tagged "Don't mark validation failures as failures"
  optionCLParser = flagCLParser Nothing (IgnoreValidation True)
