module AstInfo where

import GHC.Core ( CoreExpr, CoreBndr )
import GHC.Types.Id ( Id )

import Control.Monad.Except (ExceptT)
import Control.Monad.State.Lazy (StateT)

-- data Conversion = Conversion {
--   lhsCN     :: CoreExpr,
--   rhsCN     :: CoreExpr,
--   commentCN :: String,        -- Maybe HsExpr GhcPs to substitute
--   lDiffCN   :: CoreExpr,
--   rDiffCN   :: CoreExpr
-- }

-- data ExprInfo = LFunc String | RFunc String | Beta | LEta | REta
type SideExprInfo = Either ExprInfo ExprInfo
data ExprInfo = Func String | Postl String | Beta | Eta

data Conversion = Conversion {
  cn_lhs  :: CoreExpr,
  cn_rhs  :: CoreExpr,
  cn_info :: SideExprInfo
}

-- Add local Where to DeclConversions???
type DeclConversions = (Id, [Conversion])
type FuncDef  = (Id, CoreExpr)

data PostlDef = PostlDef {
  pstl_id     :: Id,
  pstl_binds  :: [CoreBndr],
  pstl_lhs    :: CoreExpr,
  pstl_rhs    :: CoreExpr
}

-- data AstInfo = AstInfo {
--   ast_declconvrs   :: [DeclConversions], -- List of Conversion per decl
--   ast_funcdefs     :: [FuncDef], -- List of all function definitions (decls)
--   ast_postldefs    :: [PostlDef] -- List of all postulate definitions
-- }

data CheckerST = CheckerST {
  st_declconvrs   :: [DeclConversions], -- List of Conversion per decl
  st_funcdefs     :: [FuncDef], -- List of all function definitions (decls)
  st_postldefs    :: [PostlDef] -- List of all postulate definitions
}

type CheckerM = ExceptT String (StateT CheckerST IO)

{-
  I WANT 
  to return REPORT:
    Failure: 
      [ 
        in function--X
        in step--Y
        Reason
      ]
    Succses:
      [Function]
  
  OR:
    For each function have:
      Failure:
        in Step--Y
        Reason
      Succses
  
ExceptT e (StateT s IO)
  1) Get List of functions
  2) Separate them
      Each of them or
        should be proved (A)
        is a postulate
        Just function
  3) go throught (A)
    for each create report
    update state if succses
  
  

  [Func] [Postuls] (NTP : NeedsToProve) -> [Func] [Postuls, NTP] (NeedsToProve)
  [Func]    = [Id, funcBody = (\x y z -> expr)]
  [Postuls] = [Id, lhs, rhs, fn_binds]
  NTP       = [Id, [(lhs, rhs)]]

 
 
 
 FOR LATER:
  Func to NTP => (need to rememebr list of all Funcs)
    get list of defined in where -> [Funcs] -> ...
      get list of comments
        1) all used functions should be visiable
        2) add to graph
    get 
    
  NTP       = [Id, [(lhs, rhs)]]

decide order:
  list of 'all visiable theorems at this point'
  -> list of 'all used theorems'
  theorem11 = [theorem12]
  theorem12 = [theorem11]
    where
      theorem21 = [theorem12, theorem22, theorem23, theorem31, theorem32]
        where
          theorem31 = [theorem12, theorem32]
          theorem32 = [theorem12, theorem31]
      theorem22 = [theorem12, theorem21, theorem23, theorem33, theorem34]
        where
          theorem33 = [theorem34]
          theorem34 = [theorem33]
      theorem23 = 
-}
