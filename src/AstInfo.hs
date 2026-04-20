module AstInfo where

import GHC.Core
import GHC.Types.Id

data Conversion = Conversion {
  lhs     :: CoreExpr,
  rhs     :: CoreExpr,
  comment :: String,        -- Maybe HsExpr GhcPs to substitute
  lDiff   :: CoreExpr,
  rDiff   :: CoreExpr
}

-- Add local Where to DeclConversions???
type DeclConversions = (Id, [Conversion])
type FuncDef = (Id, CoreExpr)

data AstInfo = AstInfo {
  declConvrs  :: [DeclConversions], -- List of Conversion per decl
  funcDefs    :: [FuncDef] -- List of all function definitions (decls)
}