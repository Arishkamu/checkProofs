{-# LANGUAGE RecordWildCards, FlexibleContexts#-}

module Main where

import GHC
import GHC.Paths (libdir)
import GHC.Core
import GHC.Core.Utils (cheapEqExpr)
import GHC.Utils.Outputable (showSDocUnsafe, ppr)

import Data.Generics.Uniplate.Data (universe)
import Data.Data (toConstr)
import Control.Applicative ((<|>))
import Control.Monad.IO.Class (liftIO)

import PrettyPrint
import AstInfo

main :: IO ()
main =
  runGhc (Just libdir) $ do
    dflags <- getSessionDynFlags
    _ <- setSessionDynFlags dflags

    let filePath = "/Users/arina/hse/nir/moskvinPrj/checkProofs/old/Example.hs"
    coreMod <- compileToCoreModule filePath
-- --    return (cm_binds coreModule)
    -- liftIO $ putStrLn "\n=== Core cm_binds ===\n"
    -- liftIO $ putStrLn (prettyPrint $ cm_binds coreMod)
    let astInfo = collectModule coreMod
    liftIO $ putStrLn "\n=== AstInfo ===\n"
    liftIO $ putStrLn "\n=== AstInfo ==="
    liftIO $ putStrLn "\n=== AstInfo ==="
    liftIO $ putStrLn "\n=== AstInfo ==="
    liftIO $ putStrLn (prettyPrint astInfo)
    liftIO $ putStrLn "\n===== The End: App/Main ====="


---- UTILS
onSnd :: (b -> c) -> (a, b) -> (a, c)
onSnd f (x, y) = (x, f y)


---- COLLECTING AST INFO
collectModule :: CoreModule -> AstInfo
collectModule CoreModule{..} = AstInfo {
  declConvrs = map (onSnd collectExpr) binds,
  funcDefs   = binds
} 
  where
  binds = concatMap (\bind -> case bind of
      NonRec v expr -> [(v, expr)]
      Rec vExprs ->  vExprs) 
    cm_binds

-- collectBind :: CoreBind -> [DeclConversions]
-- collectBind bind = map (onSnd collectExpr) $ 
--   case bind of
--     NonRec v expr -> [(v, expr)]
--     Rec vExprs ->  vExprs

collectExpr :: CoreExpr -> [Conversion]
collectExpr expr = map getConvrs pairs where
  argWithInfo = [(argExpr, argComm) |
    (App (App (App (Var exprName) _) argExpr) argComm) <- universe expr,
    "WithInfo" <- [showSDocUnsafe (ppr exprName)] ]
  pairs  = zip argWithInfo (drop 1 argWithInfo)
  getConvrs ((lhe, c1), (rhe, _)) = getConvrsWithDiff lhe rhe (toStr c1) (findDiff lhe rhe)
  getConvrsWithDiff lhe rhe comm (diffL, diffR) = Conversion lhe rhe comm diffL diffR
  toStr (App _ (Lit lit)) = showSDocUnsafe (ppr lit)
  toStr aaa = "WTF: " ++ show (toConstr aaa) ++ showSDocUnsafe (ppr aaa)

findDiff :: CoreExpr -> CoreExpr -> (CoreExpr, CoreExpr)
findDiff l r = 
  case cmpMaybe l r of
    Just le -> le
    Nothing -> error "findDiff: no difference found"
  where
  cmpMaybe l r 
    | cheapEqExpr l r = Nothing
    | otherwise = 
      case (l, r) of
        (App fl al, App fr ar) -> cmpMaybe fl fr <|> cmpMaybe al ar
        (Lam _ bl,  Lam _ br)  -> cmpMaybe bl br
        (Let bl el, Let br er) -> cmpBindMaybe bl br <|> cmpMaybe el er
        -- Case (Expr b) b Type [Alt b]	 
        -- Cast (Expr b) CoercionR	 
        -- Tick CoreTickish (Expr b)
        (_, _)                 -> Just (l, r)
  cmpBindMaybe (NonRec _ el) (NonRec _ er) = cmpMaybe el er
  cmpBindMaybe (Rec vels) (Rec vers) = foldr ((<|>) . uncurry cmpMaybe) Nothing (zipWith (\vl vr -> (snd vl, snd vr)) vels vers)
  -- cmpBindMaybe l r = Just (l, r)
--


-- substitute :: CoreExpr -> String
-- substitute _ = "Substitute" -- TODO: implement
-- inlineOnce :: Id -> CoreExpr -> CoreExpr -> CoreExpr
-- inlineOnce fn body expr =
--   substExpr subst expr
--   where
--     subst = extendSubst emptySubst fn body

--
--
--
--{-# LANGUAGE LambdaCase, RecordWildCards#-}
--
--import GHC
--import GHC.Hs
--import GHC.Types.SrcLoc
--import GHC.Paths (libdir)
--import GHC.Driver.Flags
--import GHC.Utils.Outputable (Outputable, showSDocUnsafe, ppr)
--import GHC.Core
--import GHC.Core.Make (mkCoreBind)
--import GHC.Driver.Pipeline (compileOne)
--import GHC.Driver.Session (setGeneralFlag, GeneralFlag(Opt_SimplifyPgm, Opt_FloatIntoLazyBindings))
--import GHC.Data.Bag (Bag, bagToList)
--
--import Control.Monad.IO.Class
--
--import System.Directory (getCurrentDirectory)
--import System.FilePath ((</>))
--
--import Data.List (intercalate)
--import Data.Generics.Uniplate.Data
--import Data.Data
--
--import Debug.Trace
--
--main :: IO ()
--main =
--  runGhc (Just libdir) $ do
--    dflags <- getSessionDynFlags
--    _ <- setSessionDynFlags dflags
--
--    let path = "/Users/arina/hse/nir/moskvinPrj/checkProofs/old/Example.hs"
--    target <- guessTarget path Nothing Nothing
--    setTargets [target]
--    load LoadAllTargets
--
--    modGraph <- depanal [] False
--    let ms = head $ mgModSummaries modGraph
--
--    let ms = head $ mgModSummaries modGraph
--
--    parsed <- parseModule ms
--
----    liftIO $ putStrLn "\n=== Parsed AST ==="
----    liftIO $ putStrLn (showSDocUnsafe (ppr (pm_parsed_source parsed)))
----
--    typed <- typecheckModule parsed
----
----    liftIO $ putStrLn "\n=== Renamed AST ==="
----    liftIO $ putStrLn (showSDocUnsafe (ppr (tm_renamed_source typed)))
----
--    liftIO $ putStrLn "\n=== Typechecked AST ==="
--    liftIO $ putStrLn (showSDocUnsafe (ppr (tm_typechecked_source typed)))
--    liftIO $ putStrLn "\n=== Core AST ==="
--
--    -- Get Core bindings
--    getModuleInfo (ms_mod_name ms) >>= \case
--      Just modInfo -> do
--        case modInfoTyThings modInfo of
--          Just tyThings -> do
--            liftIO $ putStrLn "\n=== Type Things (from Core) ==="
--            liftIO $ putStrLn $ unlines $ map (showSDocUnsafe . ppr) tyThings
--          Nothing -> liftIO $ putStrLn "No type things available"
--      Nothing -> liftIO $ putStrLn "No module info available"
--
--    liftIO $ putStrLn "\n=== AST ==="
