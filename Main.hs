module Main where

import Control.Monad.Reader
import Control.Monad.Except
import Control.Exception (try)
import Data.List
import Data.Time
import System.Directory
import System.FilePath
import System.Environment
import System.Console.GetOpt
import System.Console.Haskeline
import System.Console.Haskeline.History
import Text.Printf

import Exp.Lex
import Exp.Par
import Exp.Print
import Exp.Abs hiding (NoArg)
import Exp.Layout
import Exp.ErrM

import CTT
import Resolver
import qualified TypeChecker as TC
import qualified Eval as E

type Interpreter a = InputT IO a

-- Flag handling
data Flag = Debug | Help | Version | Time
  deriving (Eq,Show)

options :: [OptDescr Flag]
options = [ Option "d"  ["debug"]   (NoArg Debug)   "run in debugging mode"
          , Option ""   ["help"]    (NoArg Help)    "print help"
          , Option "-t" ["time"]    (NoArg Time)    "measure time spent computing"
          , Option ""   ["version"] (NoArg Version) "print version number" ]

-- Version number, welcome message, usage and prompt strings
version, welcome, usage, prompt :: String
version = "1.0"
welcome = "cubical, version: " ++ version ++ "  (:h for help)\n"
usage   = "Usage: cubical [options] <file.ctt>\nOptions:"
prompt  = "> "

lexer :: String -> [Token]
lexer = resolveLayout True . myLexer

showTree :: (Show a, Print a) => a -> IO ()
showTree tree = do
  putStrLn $ "\n[Abstract Syntax]\n\n" ++ show tree
  putStrLn $ "\n[Linearized tree]\n\n" ++ printTree tree

-- Used for auto completion
searchFunc :: [String] -> String -> [Completion]
searchFunc ns str = map simpleCompletion $ filter (str `isPrefixOf`) ns

settings :: [String] -> Settings IO
settings ns = Settings
  { historyFile    = Nothing
  , complete       = completeWord Nothing " \t" $ return . searchFunc ns
  , autoAddHistory = True }

main :: IO ()
main = do
  args <- getArgs
  case getOpt Permute options args of
    (flags,files,[])
      | Help    `elem` flags -> putStrLn $ usageInfo usage options
      | Version `elem` flags -> putStrLn version
      | otherwise -> case files of
       []  -> do
         putStrLn welcome
         runInputT (settings []) (loop flags [] [] TC.verboseEnv)
       [f] -> do
         putStrLn welcome
         putStrLn $ "Loading " ++ show f
         initLoop flags f emptyHistory
       _   -> putStrLn $ "Input error: zero or one file expected\n\n" ++
                         usageInfo usage options
    (_,_,errs) -> putStrLn $ "Input error: " ++ concat errs ++ "\n" ++
                             usageInfo usage options

-- Initialize the main loop
initLoop :: [Flag] -> FilePath -> History -> IO ()
initLoop flags f hist = do
  -- Parse and type check files
  (_,_,mods) <- imports True ([],[],[]) f
  -- Translate to TT
  let res = runResolver $ resolveModules mods
  case res of
    Left err    -> do
      putStrLn $ "Resolver failed: " ++ err
      runInputT (settings []) (putHistory hist >> loop flags f [] TC.verboseEnv)
    Right (adefs,names) -> do
      (merr,tenv) <- TC.runDeclss TC.verboseEnv adefs
      case merr of
        Just err -> putStrLn $ "Type checking failed: " ++ err
        Nothing  -> putStrLn "File loaded."
      -- Compute names for auto completion
      runInputT (settings [n | (n,_) <- names]) (putHistory hist >> loop flags f names tenv)

-- The main loop
loop :: [Flag] -> FilePath -> [(CTT.Ident,SymKind)] -> TC.TEnv -> Interpreter ()
loop flags f names tenv = do
  input <- getInputLine prompt
  case input of
    Nothing    -> outputStrLn help >> loop flags f names tenv
    Just ":q"  -> return ()
    Just ":r"  -> getHistory >>= lift . initLoop flags f
    Just (':':'l':' ':str)
      | ' ' `elem` str -> do outputStrLn "Only one file allowed after :l"
                             loop flags f names tenv
      | otherwise      -> getHistory >>= lift . initLoop flags str
    Just (':':'c':'d':' ':str) -> do lift (setCurrentDirectory str)
                                     loop flags f names tenv
    Just ":h"  -> outputStrLn help >> loop flags f names tenv
    Just str'  ->
      let (msg,str,mod) = case str' of
            (':':'n':' ':str) ->
              ("NORMEVAL: ",str,E.normal [])
            str -> ("EVAL: ",str,id)
      in case pExp (lexer str) of
      Bad err -> outputStrLn ("Parse error: " ++ err) >> loop flags f names tenv
      Ok  exp ->
        case runResolver $ local (insertIdents names) $ resolveExp exp of
          Left  err  -> do outputStrLn ("Resolver failed: " ++ err)
                           loop flags f names tenv
          Right body -> do
            x <- liftIO $ TC.runInfer tenv body
            case x of
              Left err -> do outputStrLn ("Could not type-check: " ++ err)
                             loop flags f names tenv
              Right _  -> do
                start <- liftIO getCurrentTime
                let e = mod $ E.eval (TC.env tenv) body

                -- Let's not crash if the evaluation raises an error:
                liftIO $ catch (putStrLn (msg ++ show e))
                               (\e -> putStrLn ("Exception: " ++
                                                show (e :: SomeException)))
                stop <- liftIO getCurrentTime
                -- Compute time and print nicely
                let time = diffUTCTime stop start
                    secs = read (takeWhile (/='.') (init (show time)))
                    rest = read ('0':dropWhile (/='.') (init (show time)))
                    mins = secs `quot` 60
                    sec  = printf "%.3f" (fromInteger (secs `rem` 60) + rest :: Float)
                when (Time `elem` flags) $
                   outputStrLn $ "Time: " ++ show mins ++ "m" ++ sec ++ "s"
                -- Only print in seconds:
                -- when (Time `elem` flags) $ outputStrLn $ "Time: " ++ show time
                loop flags f names tenv

-- (not ok,loaded,already loaded defs) -> to load ->
--   (new not ok, new loaded, new defs)
-- the bool determines if it should be verbose or not
imports :: Bool -> ([String],[String],[Module]) -> String ->
           IO ([String],[String],[Module])
imports v st@(notok,loaded,mods) f
  | f `elem` notok  = putStrLn ("Looping imports in " ++ f) >> return ([],[],[])
  | f `elem` loaded = return st
  | otherwise       = do
    b <- doesFileExist f
    let prefix = dropFileName f
    if not b
      then putStrLn (f ++ " does not exist") >> return ([],[],[])
      else do
        s <- readFile f
        let ts = lexer s
        case pModule ts of
          Bad s  -> do
            putStrLn $ "Parse failed in " ++ show f ++ "\n" ++ show s
            return ([],[],[])
          Ok mod@(Module (AIdent (_,name)) imp decls) ->
            let imp_ctt = [prefix ++ i ++ ".ctt" | Import (AIdent (_,i)) <- imp]
            in do
              when (name /= dropExtension (takeFileName f)) $
                error $ "Module name mismatch " ++ show (f,name)
              (notok1,loaded1,mods1) <-
                foldM (imports v) (f:notok,loaded,mods) imp_ctt
              when v $ putStrLn $ "Parsed " ++ show f ++ " successfully!"
              return (notok,f:loaded1,mods1 ++ [mod])

help :: String
help = "\nAvailable commands:\n" ++
       "  <statement>     infer type and evaluate statement\n" ++
       "  :n <statement>  normalize statement\n" ++
       "  :q              quit\n" ++
       "  :l <filename>   loads filename (and resets environment before)\n" ++
       "  :cd <path>      change directory to path\n" ++
       "  :r              reload\n" ++
       "  :h              display this message\n"
