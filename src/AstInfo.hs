{-|
Module      : AstInfo
Description : Checker state definitions.

This module defines the core data structures used by the checker and
conversion engine.
-}
module AstInfo where

import GHC (HscEnv)
import GHC.Core ( CoreExpr, CoreRule )
import GHC.Types.Id ( Id )

import Control.Monad.Except (ExceptT)
import Control.Monad.State.Lazy (StateT)

import ProofBase ( SideExprInfo )

-- | Represents a conversion between two Core expressions.
--
-- The conversion stores:
--
-- * the left-hand side expression
-- * the right-hand side expression
-- * information about operation
data Conversion = Conversion {
  -- | Left-hand side expression.
  cn_lhs  :: CoreExpr,

  -- | Right-hand side expression.
  cn_rhs  :: CoreExpr,

  -- | Information associated with the conversion.
  cn_info :: SideExprInfo
}

-- | All conversions associated with a declaration identifier.
--
-- The 'Id' identifies the declaration, while the list contains all
-- conversions known for that declaration.
type DeclConversions = (Id, [Conversion])

-- | A function definition represented by its identifier and Core body.
type FuncDef  = (Id, CoreExpr)

-- | Represents a postulate definition ready for rewrite rule.
--
-- The field 'pstl_fid' identifies the head function appearing on the
-- left-hand side of the rule.
data PostlDef = PostlDef {
  -- | Identifier of the postulate.
  pstl_id     :: Id,

  -- | Identifier of the head function appearing on the left-hand side of the rule.
  pstl_fid    :: Id,

  -- | Created Core rewrite rule.
  pstl_rule   :: CoreRule
}

-- | Global mutable checker state.
--
-- This state is threaded through the checker monad and stores all
-- discovered declarations, conversions, postulates, and environment
-- information.
data CheckerST = CheckerST {
  -- | Conversions grouped by declaration.
  st_declconvrs   :: [DeclConversions], 

  -- | All discovered function definitions.
  st_funcdefs     :: [FuncDef],

  -- | All known postulate definitions.
  st_postldefs    :: [PostlDef],

  -- | Base definitions from ProofBase.hs file.
  st_base_defs    :: [FuncDef],

  -- | Number of generated conversions.
  st_cnvrs_count  :: Int,

  -- | Identifier of the declaration currently being processed.
  st_declconvr_id :: Maybe Id,

  -- | Active GHC session environment.
  st_hscenv       :: HscEnv
}

-- | Checker monad.
--
-- Combines:
--
-- * error handling via 'ExceptT'
-- * mutable state via 'StateT'
-- * IO operations
type CheckerM = ExceptT String (StateT CheckerST IO)

-- | A failed report entry.
--
-- Contains:
--
-- * the identifier that failed
-- * an explanatory error message
type ReportFail = (Id, String)

-- | Final checker report.
--
-- The first component contains successful identifiers,
-- while the second contains failures.
type Report = ([Id], [ReportFail])
