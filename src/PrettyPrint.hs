{-# LANGUAGE RecordWildCards, FlexibleInstances #-}
module PrettyPrint (PrettyPrint, prettyPrint, prettyPrintBinds) where

import GHC.Core
import GHC.Types.Id
import GHC.Utils.Outputable (Outputable, showSDocUnsafe, ppr)
import GHC.Types.Name.Occurrence (occNameString)
import GHC.Types.Name (getOccName)

import Data.List (intercalate)
import Data.Data (toConstr)

import AstInfo

class PrettyPrint a where
  prettyPrintIdent :: Int -> a -> String
--   prettyPrintIdent ident x = showSDocUnsafe (ppr x)

prettyPrint :: (PrettyPrint a) => a -> String
prettyPrint = prettyPrintIdent 0

bslN :: Int -> String
bslN ident = "\n" ++ replicate ident ' '

prettyPrintStrs :: Int -> [String] -> String
prettyPrintStrs ident = intercalate (bslN ident)

-- instance (PrettyPrint a) => PrettyPrint (GenLocated SrcSpanAnnA a) where
--   prettyPrint (L _ x) = prettyPrint x

-- instance (Outputable a) => PrettyPrint Id where
--   prettyPrintIdent _ x = "\n" ++ replicate ident ' ' ++ showSDocUnsafe (ppr x)

instance PrettyPrint Id where
  prettyPrintIdent _ x = "ID: " ++ occNameString (getOccName x)

-- instance PrettyPrint (GenLocated SrcSpanAnnN Id) where
--   prettyPrint (L _ x) = prettyPrint x

instance PrettyPrint ExprInfo where
    prettyPrintIdent _ expr_info = case expr_info of
        Func  comment -> "Func: "  ++ comment
        Postl comment -> "Postl: " ++ comment
        Beta          -> "Beta reduction"
        Eta           -> "Eta reduction"

instance PrettyPrint Conversion where
  prettyPrintIdent ident Conversion{..} = 
    prettyPrintIdent 0 cn_info ++ " :: "
    ++ bslN (ident + 2) ++ "l: " ++ prettyPrintIdent 0 cn_lhe
    ++ bslN (ident + 2) ++ "r: " ++ prettyPrintIdent 0 cn_rhe
    -- ++ showSDocUnsafe (ppr cn_lhe) ++ " => " ++ showSDocUnsafe (ppr cn_rhe) 
    -- ++
    -- bslN ident       ++ "Different constructors: " ++ show (toConstr lDiffCN) ++ " vs " ++ show (toConstr rDiffCN) ++
    -- bslN (ident + 2) ++ "l: " ++ prettyPrint lDiffCN ++ 
    -- bslN (ident + 2) ++ "r: " ++ prettyPrint rDiffCN

instance PrettyPrint AstInfo where
  prettyPrintIdent ident AstInfo{..} =
    "===== AstInfo =====" 
    ++ bslN ident ++ "Ast_declconvrs:" ++ prettyPrintStrs  (ident + 2) (concatMap makePretty ast_declconvrs)  
    ++ bslN ident ++ "Ast_funcDefs:"    ++ prettyPrintIdent (ident + 2) (ast_funcdefs)
    ++ bslN ident ++ "Ast_postlDefs:"   ++ prettyPrintIdent (ident + 2) (ast_postldefs)

    where
    makePretty (decl, convrs) =
        (bslN (ident + 2) ++ "DeclName: " ++  prettyPrintIdent (ident + 2) decl) 
        : map (prettyPrintIdent (ident + 4)) convrs

-- -- Represent: LHsBindLR GhcTc
-- --instance PrettyPrint (HsBindLR GhcTc GhcTc) where
-- --  prettyPrint (L _ bind) = prettyPrint bind

prettyPrintBinds :: [(Id, CoreExpr)] -> String
prettyPrintBinds binds = intercalate (bslN 2) $ map prettyPrintBind binds
  where
    prettyPrintBind (fnId, fnBody) = "Function: " ++ prettyPrint fnId ++ "\nBody: " ++ prettyPrintExpr fnBody

prettyPrintExpr :: CoreExpr -> String
prettyPrintExpr expr = case expr of
  Lam args body -> "Lam: " ++ "\n    " ++ showSDocUnsafe (ppr args) ++ "\n" ++ prettyPrintExpr body
  App f arg -> "App: " ++ prettyPrintExpr f ++ "\n to " ++ prettyPrintExpr arg
  Var v -> "Var: " ++ showSDocUnsafe (ppr v) 
  _ -> "NotImpl: " ++ showSDocUnsafe (ppr expr)

-- instance PrettyPrint CoreBind where
--     prettyPrintIdent ident (NonRec v expr) =
--       "NonRec: " ++ prettyPrintIdent (ident + 2) v 
--     --   ++ "\n" ++ prettyPrintIdent (ident + 2) expr
--     prettyPrintIdent ident (Rec vExprs) =
--       "Rec: " ++ intercalate (bslN (ident + 2)) (map (\(v, e) -> prettyPrintIdent (ident + 4) v {- ++ "\n" ++ prettyPrintIdent (ident + 4) e -}) vExprs)

-- instance PrettyPrint (HsBindLR GhcTc GhcTc) where
--   prettyPrint bind =
-- --  show (toConstr bind) ++ " :: " ++ (showSDocUnsafe (ppr bind))
--     case bind of
--       fb@FunBind{ fun_matches = mg } -> "FUNBIND: " ++ "\nID:" ++ showSDocUnsafe (ppr (unLoc (fun_id fb))) ++ "\n" ++ (showSDocUnsafe (ppr bind))
-- --      analyzeMatchGroup mg
-- --          PatBind{} -> []
-- --          VarBind{} ->
-- --          PatSynBind{} -> "PatSynBind"
--       (XHsBindsLR a) -> "XHsBindsLR" ++ " :: " ++ prettyPrint (abs_binds a)
--       _ -> show (toConstr bind) ++ " :: " ++ (showSDocUnsafe (ppr bind))

instance PrettyPrint CoreExpr where
--   prettyPrintIdent _ (App f arg) = "APP " ++ " :: " ++ "\nF: " ++ (showSDocUnsafe (ppr f)) ++ "\nA: " ++ (showSDocUnsafe (ppr arg))
  prettyPrintIdent _ expr = show (toConstr expr) ++ " :: " ++ (showSDocUnsafe (ppr expr))

instance (PrettyPrint a, PrettyPrint b) => PrettyPrint (a, b) where
  prettyPrintIdent ident (x, y) = bslN ident ++ "(" 
    ++ "\n" ++ prettyPrintIdent (ident + 2) x 
    ++ "\n" ++ prettyPrintIdent (ident + 2) y
    ++ bslN ident ++ ")"

instance (PrettyPrint a, PrettyPrint b, PrettyPrint c) => PrettyPrint (a, b, c) where
  prettyPrintIdent ident (x, y, z) = bslN ident ++ "(" 
    ++ "\n" ++ prettyPrintIdent (ident + 2) x 
    ++ "\n" ++ prettyPrintIdent (ident + 2) y 
    ++ "\n" ++ prettyPrintIdent (ident + 2) z 
    ++ bslN ident ++ ")"


instance (PrettyPrint a) => PrettyPrint [a] where
  prettyPrintIdent ident as = intercalate (bslN ident) $ map (prettyPrintIdent (ident + 2)) as

instance (PrettyPrint a) => PrettyPrint (Either String a) where
  prettyPrintIdent ident (Left e)  = "Either-Left:"  ++ bslN (ident + 2) ++ e
  prettyPrintIdent ident (Right a) = "Either-Right:" ++ bslN (ident + 2) ++ prettyPrint a

instance (PrettyPrint a) => PrettyPrint (Either a a) where
  prettyPrintIdent ident (Left l)  = "L-" ++ prettyPrintIdent ident l
  prettyPrintIdent ident (Right r) = "R-" ++ prettyPrintIdent ident r


-- instance (PrettyPrint a) => PrettyPrint (Bag a) where
--   prettyPrint = prettyPrint . bagToList