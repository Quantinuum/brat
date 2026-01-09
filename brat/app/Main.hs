import Brat.Compiler
import Brat.Machine (runInterpreter)

import Control.Monad (when)
import Options.Applicative

data Options = Opt {
  ast     :: Bool,
  dot     :: String,
  compile :: Bool,
  file    :: String,
  libs    :: String,
  raw     :: Bool,
  runFunc :: String
}

compileFlag :: Parser Bool
compileFlag = switch (long "compile" <> short 'c' <> help "Compile to TIERKREIS")

astFlag = switch (long "ast" <> help "Print desugared BRAT syntax tree")

rawFlag = switch (long "raw" <> help "Print raw BRAT syntax tree")

dotOption = strOption (long "dot" <> value "" <> help "Write graph in Dot format to the specified file")

libOption = strOption (long "lib" <> value "" <> help "Look in extra directories for libraries (delimited with ;)")

runFuncOption = strOption (long "run" <> value "" <> help "Run function with interpreter (must take no arguments)")

opts :: Parser Options
opts = Opt <$> astFlag <*> dotOption <*> compileFlag <*> strArgument (metavar "FILE") <*> libOption <*> rawFlag <*> runFuncOption

-- Parse a list of library directories delimited by a semicolon
parseLibs :: String -> [String]
parseLibs "" = []
parseLibs libs = case break (==':') libs of
  (lib, []) -> if null lib then [] else [lib]
  ([], _:cs) -> parseLibs cs
  (lib, _:cs) -> lib : parseLibs cs

main = do
  Opt{..} <- execParser (info opts (progDesc "Compile a BRAT program"))
  when (ast || raw) $ printAST raw ast file
  let libDirs = parseLibs libs
  when (dot /= "") $ writeDot libDirs file dot
  if compile then compileAndPrintFile libDirs file
  else if runFunc /= "" then runInterpreter libDirs file runFunc
                        else printDeclsHoles libDirs file
