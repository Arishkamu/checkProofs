module ProofBase where

data SideExprInfo = L ExprInfo | R ExprInfo | QED | Postulate
data ExprInfo = Decl String | Prop String | Beta | Eta | DeclRec String Integer
-- data WithInfo a = WithInfo { value :: a, info :: SideExprInfo}

(--.) :: a -> SideExprInfo -> a
(--.) x _ = x


infixl 0 ===
(===) :: a -> a -> a
(===) x y = y

