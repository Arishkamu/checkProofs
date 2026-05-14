module AstInfo where

import GHC (HscEnv)
import GHC.Core ( CoreExpr, CoreRule )
import GHC.Types.Id ( Id )
import GHC.Utils.Outputable (Outputable)

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
data SideExprInfo = L ExprInfo | R ExprInfo | QED | Postulate
data ExprInfo = Decl String | Prop String | Beta | Eta | DeclRec String Integer

data Conversion = Conversion {
  cn_lhs  :: CoreExpr,
  cn_rhs  :: CoreExpr,
  cn_info :: SideExprInfo
}

-- Add local Where to DeclConversions???
type DeclConversions = (Id, [Conversion])
type FuncDef  = (Id, CoreExpr)

-- TODO store only pstl_id and CoreRule
-- data PostlDef = PostlDef {
--   pstl_id     :: Id,
--   pstl_binds  :: [CoreBndr],
--   pstl_lhs    :: CoreExpr,
--   pstl_rhs    :: CoreExpr
-- }
data PostlDef = PostlDef {
  pstl_id     :: Id,
  pstl_fid    :: Id, -- id for key function in lhs rule
  pstl_rule   :: CoreRule
}

-- data AstInfo = AstInfo {
--   ast_declconvrs   :: [DeclConversions], -- List of Conversion per decl
--   ast_funcdefs     :: [FuncDef], -- List of all function definitions (decls)
--   ast_postldefs    :: [PostlDef] -- List of all postulate definitions
-- }

data CheckerST = CheckerST {
  st_declconvrs   :: [DeclConversions], -- List of Conversion per decl
  st_funcdefs     :: [FuncDef], -- List of all function definitions (decls)
  st_postldefs    :: [PostlDef], -- List of all postulate definitions
  st_cnvrs_count  :: Int,
  st_declconvr_id :: Maybe Id,
  st_hscenv       :: HscEnv
}

-- data CheckerST = CheckerST {
--   -- stay the same
--   st_declconvrs   :: [DeclConversions], -- List of Conversion per decl
--   st_funcdefs     :: [FuncDef], -- List of all function definitions (decls)
--   st_postldefs    :: [PostlDef], -- List of all postulate definitions
--   st_hscenv       :: HscEnv
--   -- pass throught
--   st_newpostls    :: [PostlDef], -- List of all postulate definitions
--   -- new for each conversion
--   st_alphaEq      :: 
--   st_cnvrs_count  :: Int,
--   st_declconvr_id :: Id,
-- }

type CheckerM = ExceptT String (StateT CheckerST IO)

type Report = ([Id], [String])

{-
  I WANT 
  to return REPORT:
    Failure: 
      [ 
        in function--X
        in step--Y
        Reason
      ]
    Success:
      [Function]
  
  OR:
    For each function have:
      Failure:
        in Step--Y
        Reason
      Success
  
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
