import Brat.Compiler

import Control.Monad (when)
import Options.Applicative
import Brat.Compile.Interpreter (Value(IntV))

data Options = Opt {
  ast     :: Bool,
  dot     :: String,
  compile :: Bool,
  run     :: String,
  runArgs :: [Int],
  file    :: String,
  libs    :: String,
  raw     :: Bool
}

compileFlag :: Parser Bool
compileFlag = switch (long "compile" <> short 'c' <> help "Compile to TIERKREIS")

runOption = strOption (long "run" <> short 'r' <> value "" <> help "Run in interpreter")

runArgsOptions = many $ option auto (long "args" <> help "Run in interpreter")

astFlag = switch (long "ast" <> help "Print desugared BRAT syntax tree")

rawFlag = switch (long "raw" <> help "Print raw BRAT syntax tree")

dotOption = strOption (long "dot" <> value "" <> help "Write graph in Dot format to the specified file")

libOption = strOption (long "lib" <> value "" <> help "Look in extra directories for libraries (delimited with ;)")

opts :: Parser Options
opts = Opt <$> astFlag <*> dotOption <*> compileFlag <*> runOption <*> runArgsOptions <*> strArgument (metavar "FILE") <*> libOption <*> rawFlag

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
  if compile then compileAndPrintFile libDirs file else
    if run /= "" then runFileAndPrintResults libDirs file (Just run) (IntV <$> runArgs) else printDeclsHoles libDirs file
