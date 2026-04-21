module AstInfo where

import GHC.Core
import GHC.Types.Id

-- data Conversion = Conversion {
--   lhsCN     :: CoreExpr,
--   rhsCN     :: CoreExpr,
--   commentCN :: String,        -- Maybe HsExpr GhcPs to substitute
--   lDiffCN   :: CoreExpr,
--   rDiffCN   :: CoreExpr
-- }

data ExprInfo = LFunc String | RFunc String | Beta | LEta | REta

data Conversion = Conversion {
  cn_lhe  :: CoreExpr,
  cn_rhe  :: CoreExpr,
  cn_info :: ExprInfo
}

-- Add local Where to DeclConversions???
type DeclConversions = (Id, [Conversion])
type FuncDef = (Id, CoreExpr)

data AstInfo = AstInfo {
  ast_declconvrs  :: [DeclConversions], -- List of Conversion per decl
  ast_funcdefs    :: [FuncDef] -- List of all function definitions (decls)
}