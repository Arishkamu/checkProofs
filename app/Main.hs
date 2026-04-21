{-# LANGUAGE RecordWildCards, FlexibleContexts#-}

module Main where

import GHC
import GHC.Paths (libdir)
import GHC.Core
import GHC.Core.Utils (cheapEqExpr)
import GHC.Core.FVs (exprFreeVars)
import GHC.Core.Subst
import GHC.Types.Var.Env
import GHC.Types.Unique.Set
import GHC.Utils.Outputable (showSDocUnsafe, ppr)

import GHC.Types.Id
import GHC.Core.Opt.Arity

import GHC.Types.Unique.Supply
import GHC.Driver.Env
import GHC.Core.Opt.Simplify.Monad
import GHC.Core.Opt.Pipeline
import GHC.Core.Opt.Simplify.Env
import GHC.Runtime.Context
import GHC.Driver.Config.Core.Opt.Simplify
import GHC.Unit.External
import GHC.Core.FamInstEnv
import GHC.Core.Opt.Simplify.Iteration
import GHC.Core.Opt.Simplify
import GHC.Core.Rules
import GHC.Core.Stats
import GHC.Driver.Monad
import GHC.Core.Map.Type

import Data.Generics.Uniplate.Data (universe)
import Data.Data (toConstr)
import Data.List (intercalate)
import Data.Maybe
import Control.Applicative ((<|>))
import Control.Monad.IO.Class (liftIO)

import Debug.Trace

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
    -- liftIO $ putStrLn (printBindsStr flattenBinds $ cm_binds coreMod)
    liftIO $ putStrLn "\n=== Core cm_types ===\n"
    liftIO $ putStrLn (showSDocUnsafe $ ppr $ cm_types coreMod)
    let astInfo = collectModule coreMod
    liftIO $ putStrLn "\n=== AstInfo ===\n"
    liftIO $ putStrLn "\n=== AstInfo ==="
    liftIO $ putStrLn "\n=== AstInfo ==="
    liftIO $ putStrLn "\n=== AstInfo ==="
    liftIO $ putStrLn (prettyPrint astInfo)

    liftIO $ putStrLn "\n=== END AstInfo ==="
    -- let aaa = (checkAllConversions astInfo)
    -- liftIO $ putStrLn (intercalate "\n\n" (map fst aaa))
    -- let aaa = map lhsCN $ concatMap snd (declConvrs astInfo)

    session <- getSession
    -- let bbb = filter isJust $ map snd aaa
    -- let b = head bbb
    -- let bb = head $ drop 1 bbb
    -- liftIO $ putStrLn $ prettyPrint (fromJust b)
    -- liftIO $ putStrLn $ prettyPrint (fromJust bb)
    -- liftIO $ simpExpr session (fromJust b)
    -- liftIO $ simpExpr session (fromJust bb)
    -- liftIO $ putStrLn $ prettyPrint (aaa !! 7)
    -- let resSM = simpExpr2 dflags (aaa !! 7)

    -- liftIO $ putStrLn $ prettyPrint res
    -- liftIO $ putStrLn $ prettyPrint res

    -- liftIO $ putStrLn $ intercalate "\n" $ concatMap (printBind 0) (cm_binds coreMod)

    let fDefId = findIdByComm "=." (funcDefs astInfo)
    let (fnId, fnBody) = (filter (\(fn,_) -> fn == fDefId) (funcDefs astInfo)) !! 0

    liftIO $ putStrLn "\n-----------fDef-----------"
    liftIO $ putStrLn $ prettyPrint (fnId, fnBody)

    let doubleCN = (concatMap snd $ declConvrs astInfo) !! 6
    let singleCN = (concatMap snd $ declConvrs astInfo) !! 7

    let (strS, singleCE) = checkConversion singleCN (funcDefs astInfo)
    let (strD, doubleCE) = checkConversion doubleCN (funcDefs astInfo)
    liftIO $ putStrLn "\n-----------Checking conversion for singleCN-----------"
    liftIO $ putStrLn strS
    liftIO $ putStrLn "\n-----------Checking conversion for doubleCN-----------"
    liftIO $ putStrLn strD

    -- let mwtDoubleCN = myWalkTest (lhsCN doubleCN)
    -- let mwtDoubleCE = myWalkTest $ fromJust doubleCE
    -- liftIO $ putStrLn "\n-----------Walking doubleCE-----------"
    -- liftIO $ putStrLn $ prettyPrint mwtDoubleCE
    -- liftIO $ putStrLn "\n-----------Walking doubleCN-----------"
    -- liftIO $ putStrLn $ prettyPrint mwtDoubleCN
    let doubleLastArg = case lhsCN doubleCN of
          App f arg -> arg
    let doubleCESingle = case fromJust doubleCE of
          App f arg -> App f doubleLastArg
    liftIO $ putStrLn "\n-----------Walking doubleCESingle-----------"
    liftIO $ putStrLn $ prettyPrint doubleCESingle
    liftIO $ putStrLn "\n-----------Simplify singleCE-----------"
    r1 <- liftIO $ simpExpr session doubleCESingle fnId fnBody
    liftIO $ putStrLn "\n-----------Subst lets-----------"
    liftIO $ putStrLn $ prettyPrint $ inlineLets r1

    let (dL, dR) = (inlineLets r1, (rhsCN doubleCN))
    liftIO $ putStrLn "\n-----------Check equality-----------"
    liftIO $ putStrLn $ prettyPrint dL
    liftIO $ putStrLn $ prettyPrint dR
    liftIO $ putStrLn $ "isEqual: " ++ show (( deBruijnize dL) == (deBruijnize dR))



    liftIO $ putStrLn "\n-----------myWalkTest singleCN-----------"
    liftIO $ putStrLn $ prettyPrint $ myWalkTest (lhsCN singleCN)
    let easySubstResD = easySubstFunc (lhsCN doubleCN) fnId fnBody
    liftIO $ putStrLn "\n----------- easySubstFunc -----------"
    liftIO $ putStrLn $ prettyPrint easySubstResD
    r3 <- liftIO $ simpExpr session easySubstResD fnId fnBody
    -- liftIO $ putStrLn $ showSDocUnsafe $ ppr $ exprFreeVars doubleCESingle

    -- let mwtDouble = myWalkTest (lhsCN doubleCN)
    -- liftIO $ putStrLn $ prettyPrint (lhsCN doubleCN)
    -- liftIO $ putStrLn $ prettyPrint (rhsCN doubleCN)
    -- liftIO $ putStrLn "\n-----------Walking Double Lhs-----------"
    -- liftIO $ putStrLn $ prettyPrint mwtDouble

    -- let arg1 = mwtDouble !! 1
    -- let arg2 = mwtDouble !! 2
    -- let arg3 = mwtDouble !! 3
    -- let arg4 = mwtDouble !! 4
    -- let arg5 = mwtDouble !! 5
    -- let newBody = App (App (App (App (App fnBody arg1) arg2) arg3) arg4) arg5
    -- liftIO $ putStrLn "\n-----------Simplify fn body-----------"
    -- liftIO $ simpExpr session newBody
    -- liftIO $ putStrLn $ showSDocUnsafe $ ppr $ exprFreeVars newBody



    liftIO $ putStrLn "\n===== The End: App/Main ====="

alphaEqExpr :: CoreExpr -> CoreExpr -> Bool
alphaEqExpr lhs rhs = (deBruijnize lhs) == (deBruijnize rhs)

inlineLets :: CoreExpr -> CoreExpr
inlineLets expr =
  case expr of
    Let (NonRec b rhs) body ->
      inlineLets (easySubst body b rhs)

    App f x ->
      App (inlineLets f) (inlineLets x)

    Lam b e ->
      Lam b (inlineLets e)

    _ -> expr

easySubstFunc :: CoreExpr -> Id -> CoreExpr -> CoreExpr
easySubstFunc expr fnId fnBody = foldl App newf as
  where
  getFunc e =
    case e of 
      App fa arg -> arg : (getFunc fa)
      _          -> [e]
  (f:as) = reverse $ getFunc expr
  newf   = easySubst f fnId fnBody
  -- (x:[]) -> error "easySubstFunc: not enough arguments"
  -- []     -> error "easySubstFunc: empty expression"
  -- (f:as) -> (f, as)
  -- Lam b (Expr b)	 
  -- Let (Bind b) (Expr b)	 
  -- !ignore
  -- Case (Expr b) b Type [Alt b]	 
  -- Cast (Expr b) CoercionR	 
  -- Tick CoreTickish (Expr b)	
  -- !easy
  -- Var Id	 
  -- Lit Literal	 
  -- Type Type	 
  -- Coercion Coercion

easySubst :: CoreExpr -> Id -> CoreExpr -> CoreExpr
easySubst expr fnId fnBody = reslDif
  where
    delOneTScope = InScope $ delOneFromUniqSet (exprFreeVars expr) fnId 
    subst = extendSubst (mkEmptySubst delOneTScope) fnId fnBody
    reslDif = substExpr subst expr

myWalkTest :: CoreExpr -> [CoreExpr]
myWalkTest expr@(App f arg) = myWalkTest f ++ [arg]
myWalkTest expr@(Var v) = [expr]
myWalkTest expr@(Lam a1 a2) = [expr]
myWalkTest expr = error $ "myWalkTest: unexpected expression form: " ++ showSDocUnsafe (ppr expr) ++ "\nToConstr: " ++ show (toConstr expr)

simpExpr :: HscEnv -> CoreExpr -> Id -> CoreExpr -> IO CoreExpr
simpExpr hscEnv expr fnId fnBody = do
  putStrLn $ "\n=== Simplified expression 1 ===\n" ++ showSDocUnsafe (ppr expr)
  let logger = hsc_logger hscEnv
  eu_cache <- initExternalUnitCache
  let dflags = hsc_dflags hscEnv

  let opts = initSimplifyExprOpts dflags (hsc_IC hscEnv)

  ce <- simplifyExprMy logger eu_cache opts expr fnId fnBody
  putStrLn $ "\n=== Simplified expression ===\n" ++ showSDocUnsafe (ppr ce)
  return ce

simplifyExprMy logger euc opts expr fnId fnBody
  = do  { eps <- eucEPS euc ;
        ; let fam_envs = ( eps_fam_inst_env eps
                         , extendFamInstEnvList emptyFamInstEnv $ se_fam_inst opts
                         )
              simpl_env = mkSimplEnv (se_mode opts) fam_envs
              my_in_scope = (getInScope simpl_env) `extendInScopeSetSet` (exprFreeVars expr)
              my_env = setInScopeSet simpl_env my_in_scope
              my_env_two = GHC.Core.Opt.Simplify.Env.extendIdSubst my_env fnId (mkContEx my_env fnBody)
              -- delOneVSet = delOneFromUniqSet (exprFreeVars expr) fnId
              -- my_env_two = setInScopeSet my_env $ (getInScope my_env) `extendInScopeSetSet` delOneVSet
              top_env_cfg = se_top_env_cfg opts
              read_eps_rules = eps_rule_base <$> eucEPS euc
              read_ruleenv = updExternalPackageRules emptyRuleEnv <$> read_eps_rules

        ; let sz = exprSize expr

        ; (expr', counts) <- initSmpl logger read_ruleenv top_env_cfg sz $
                             simplExpr my_env_two expr

        ; return expr'
        }


simpExpr2 :: DynFlags -> CoreExpr -> SimplM CoreExpr
simpExpr2 dflags expr = do
  let simpEnv = mkSimplEnv (initGentleSimplMode dflags) (emptyFamInstEnv, emptyFamInstEnv)
  ce <- simplExpr simpEnv expr
  liftIO $ putStrLn "\nSIMPL EXPR -------------\n"
  liftIO $ putStrLn $ prettyPrint ce
  return ce


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
  binds = flattenBinds cm_binds

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

checkAllConversions :: AstInfo -> [(String, Maybe CoreExpr)]
checkAllConversions AstInfo{..} = map (`checkConversion` funcDefs) (concatMap snd declConvrs)

checkConversion :: Conversion -> [FuncDef] -> (String, Maybe CoreExpr)
checkConversion convrs funDefs 
  | commentCN convrs == "\"(=.)\"#" = (showSDocUnsafe (ppr reslDif) ++ " ==?== " ++ showSDocUnsafe (ppr (rhsCN convrs)), Just reslDif)
  | otherwise = ("No changes. Not a '=.' application. Comment: " ++ commentCN convrs, Nothing)
  where
    idComm = findIdByComm "=." funDefs
    (fnId, fnBody) = case filter (\(fn,_) -> fn == idComm) funDefs of
      body:[] -> body
      [] -> error $ "checkConversion: no function found for comment " ++ commentCN convrs
      _ -> error $ "checkConversion: multiple functions found for comment " ++ commentCN convrs
    -- reslDif = substExpr subst (lDiffCN convrs)
    delOneTScope = InScope $ delOneFromUniqSet (exprFreeVars (lhsCN convrs)) fnId 
    subst = extendSubst (mkEmptySubst delOneTScope) fnId fnBody
    reslDif = substExpr subst (lhsCN convrs)
    -- reslDif = trace ("\nTRACE: " 
    --   ++ "\nfnBody: " ++ showSDocUnsafe (ppr fnBody) 
    --   ++ "\nfnBody FV: " ++ showSDocUnsafe (ppr (exprFreeVars fnBody)) 
    --   ++ "\ntarget: " ++ showSDocUnsafe (ppr (lDiffCN convrs))
    --   ++ "\ntarget FV: " ++ showSDocUnsafe (ppr (exprFreeVars (lDiffCN convrs)))
    --   ++ "\ntarget FV: " ++ showSDocUnsafe (ppr delOneTG)) 
    --   (lDiffCN convrs)

findIdByComm :: String -> [FuncDef] -> Id
findIdByComm comm funDefs = 
  case filter (\(fn,_) -> prettyPrint fn == "ID: " ++ comm) funDefs of
    (fn, _):[] -> fn
    [] -> error $ "findIdByComm: no function found for comment " ++ comm ++ "\nAvailable functions: " ++ intercalate ", " (map (prettyPrint . fst) funDefs)
    _ -> error $ "findIdByComm: multiple functions found for comment " ++ comm

findId :: Conversion -> Id
findId Conversion{..} = 
  case lDiffCN of
    App (Var fId) _ -> fId
    App aaa@(App bbb@(App ccc _) _) _ -> error $ "findId: not an application of a function on the left-hand-diff side." ++ 
      prettyPrint lDiffCN ++ "\nToConstr: " ++ show (toConstr lDiffCN) 
        ++ "\nAAA: " ++ show (toConstr aaa) ++ " :: " ++ showSDocUnsafe (ppr aaa) 
        ++ "\nBBB: " ++ show (toConstr bbb) ++ " :: " ++ showSDocUnsafe (ppr bbb)
        ++ "\nCCC: " ++ show (toConstr ccc) ++ " :: " ++ showSDocUnsafe (ppr ccc)
    _ -> error $ "findId: not an application of a function on the left-hand-diff side." ++ prettyPrint lDiffCN ++ "\nToConstr: " ++ show (toConstr lDiffCN)  





-- -------- SUBST and B-reduction just for function
-- App (App (App func arg1) arg2) arg3 -- if Arity nor right ignore
-- I want to: take funcBody and subst arg1, arg2, arg3


-- -- copy SubstExpr
-- substExprFuncOnce :: Subst -> CoreExpr -> CoreExpr
-- substExprFuncOnce = substExprFunc False

-- substExprFunc :: Bool -> Subst -> CoreExpr -> CoreExpr
-- substExprFunc subst wasSubst expr = snd $ go False expr
--   where
--     go True expr                  = expr

--     go wasSubst (Var v)           = lookupIdSubst subst v
--     go wasSubst (App fun arg)     = (wasSubst'', App fun' arg')
--                                   where
--                                     (wasSubst', fun') = go wasSubst fun
--                                     (wasSubst'', arg') = go wasSubst' arg
--     go wasSubst (Cast e co)       = Cast (go wasSubst e) co
--     go wasSubst (Tick tickish e)  = mkTick tickish (go wasSubst e)
--     go wasSubst (Lam bndr body)   = Lam bndr' (substExprFunc subst' body)
--                                   where
--                                     (subst', bndr') = substBndr subst bndr
--     go wasSubst (Let bind body)   = Let bind' (substExprFunc subst' body)
--                                   where
--                                     (subst', bind') = substBind subst bind
--     go wasSubst (Case scrut bndr ty alts) = Case (go scrut) bndr' (substTyUnchecked subst ty) (map (go_alt subst') alts)
--                                   where
--                                     (subst', bndr') = substBndr subst bndr
--     go _ expr       = expr


--     go_alt subst (Alt con bndrs rhs) = Alt con bndrs' (substExpr subst' rhs)
--                                  where
--                                    (subst', bndrs') = substBndrs subst bndrs

-- substBind subst (NonRec bndr rhs)
--   = (subst', NonRec bndr' (substExpr subst rhs))
--   where
--     (subst', bndr') = substBndr subst bndr

-- substBind subst (Rec pairs)
--    = (subst', Rec (bndrs' `zip` rhss'))
--    where
--        (bndrs, rhss)    = unzip pairs
--        (subst', bndrs') = substRecBndrs subst bndrs
--        rhss' = map (substExpr subst') rhss



printExpr :: Int -> CoreExpr -> String
printExpr ident expr = show (toConstr expr) ++ ": " ++ "exprArity: " ++ show (exprArity expr) ++ " " ++ case expr of
  App fn arg -> ninp2 ++ printExpr' fn ++ ninp0  ++ "to" ++ ninp2 ++ printExpr' arg
  Lam x expr -> showSDocUnsafe (ppr x) ++ " ->" ++ ninp2 ++ printExpr' expr	 
  Let bind expr	-> printBindStr bind ++ ninp2 ++ "in" ++ ninp2 ++ printExpr' expr 
  _ -> ninp2 ++ showSDocUnsafe (ppr expr)
  where
  ninp0 = "\n" ++ replicate (ident) ' '
  ninp2 = "\n" ++ replicate (ident + 2) ' '
  printExpr' = printExpr (ident + 2)
  printBindStr bind = intercalate ninp2 (printBind ident bind)

printBind :: Int -> CoreBind -> [String]
printBind ident bind = map (\(v, e) -> ninp2 ++ "BVr: " ++ showSDocUnsafe (ppr v) ++ ninp2 ++ "BExp: " ++ printExpr' e) (flattenBinds [bind])
  where
  ninp2 = "\n" ++ replicate (ident + 2) ' '
  printExpr' = printExpr (ident + 2)

-- substitute :: CoreExpr -> Id -> CoreExpr -> CoreExpr
-- substitute target fId fBody = substExpr (extendSubst emptySubst fId fBody) target

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



--   "(=.)"# :: 
--   \ (x_axd :: a_aEF) -> f_axa (=. @b_aEE @c_aEC @a_aEF g_axb h_axc x_axd) 
--     => \ (x_axe :: a_aEF) -> f_axa (g_axb (h_axc x_axe))
--     Different constructors: App vs Var
--       l: App :: =. @b_aEE @c_aEC @a_aEF g_axb h_axc
--       r: Var :: g_axb



--   "(=.)"# :: 
--   \ (x_axd :: a_aEF) -> f_axa (=. @b_aEE @c_aEC @a_aEF g_axb h_axc x_axd) 
--     => \ (x_axe :: a_aEF) -> f_axa (g_axb (h_axc x_axe))
--     Different constructors: App vs Var
--       l: App :: =. @b_aEE @c_aEC @a_aEF g_axb h_axc x_axd
--       r: Var :: g_axb (h_axc x_axe)


-- Lam :: \ (@b_aCz)           -> b_aEE
--   (@c_aCA)                  -> c_aEC
--   (@a_aCB)                  -> a_aEF
--   (f_ahy :: b_aCz -> c_aCA) -> g_axb
--   (g_ahz :: a_aCB -> b_aCz) -> h_axc
--   (x_ahA :: a_aCB) ->       -> x_axd
--   f_ahy (g_ahz x_ahA)       -> g_axb (h_axc x_axd)

-- \ (x_axd :: a_aEF) ->
--   f_axa
--     ((\ (@b_aCz)
--         (@c_aCA)
--         (@a_aCB)
--         (f_ahy :: b_aCz -> c_aCA)
--         (g_ahz :: a_aCB -> b_aCz)
--         (x_ahA :: a_aCB) ->
--         f_ahy (g_ahz x_ahA))
--        @b_aEE @c_aEC @a_aEF g_axb h_axc x_axd) ==?== \ (x_axe :: a_aEF) -> f_axa (g_axb (h_axc x_axe))