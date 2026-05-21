module ExampleInst where

-- import ProofBase
-- import Prelude hiding ((.), ($), id, flip, Applicative(..))
-- import GHC.Internal.Base hiding (Functor, Functor Maybe)


{-
infixr 9 .
(.)    :: (b -> c) -> (a -> b) -> a -> c
(.) f g = \x -> f (g x)

infixr 0 $
($)    :: (a -> b) -> a -> b
($) f x = f x

id                      :: a -> a
id x                    =  x

flip :: (a -> b -> c) -> b -> a -> c
flip f x y              =  f y x



class Functor f where 
  fmap :: (a -> b) -> f a -> f b

instance Functor Maybe where
  fmap _ Nothing  = Nothing     -- fmap (1)
  fmap g (Just a) = Just (g a)  -- fmap (2)

class Functor f => Applicative f where
  pure :: a -> f a
  (<*>) :: f (a -> b) -> f a -> f b

instance Applicative Maybe where
  pure = Just                   -- pure
  Nothing <*> _  = Nothing      -- <*> (1)
  Just g  <*> x  = fmap g x     -- <*> (2)

res4 :: Maybe Int -> Maybe Int
res4 Nothing = 
      fmap (7 +) Nothing  --. L (Def  "fmap")
  === Nothing             --. QED


-- fmap g v  =  pure g <*> v
ap0LawMaybe :: (a -> b) -> Maybe a -> Maybe b
ap0LawMaybe g v = 
     pure g <*> v     --. L (Inst "pure") -- pure
 === Just g <*> v     --. L (Inst "<*>")-- (<*>) (2)
 === fmap g v         --. QED






class Inst a where 
  mapmap :: [a] -> String
  pampam :: a -> (a -> String) -> String

instance Inst (Maybe b) where
  pampam a f = f a
  mapmap []  = "0"     -- fmap (1)
  mapmap _ = "a"  -- fmap (2)

instance Inst (Either b b) where
  mapmap _  = "eqi"     -- fmap (1)
  pampam a f = f a

res5 :: [Maybe Int] -> String
res5 a = 
      (mapmap a) --. L (Inst "mapmap")
  === "9"        --. QED

res56 :: Maybe String -> String
res56 a = 
      (pampam a (\_ -> "AAA")) --. L (Inst "pampam")
  === "AAA"        --. QED

class (Eq a, Show a) => C a where
  ccc :: a -> String

instance (Eq a, Show a) => C (Maybe a) where
  ccc a = show a

res6 :: Maybe Int -> String
res6 (Just 1) = 
      ccc (Just 1) --. L (Def  "ccc")
  === "Nothing"   --. QED

-}

{-
class Functor m => AltMonad m where 
  ret :: a -> m a
  joi :: m (m a) -> m a


-- returnFREE :: Functor m => (forall a. a -> m a) -> (a -> b) -> a -> m b
-- returnFREE r f =  
--      (r . f)      --. Postulate
--  === ((id (fmap f)) . r) --. QED

returnFREE :: Functor m => (forall a. a -> m a) -> (a -> b) -> a -> m b
returnFREE r f =  
     (fmap f . r) --. Postulate
 === (r . f)      --. QED


-- {-# RULES
-- "my_returnFREE/base"
--   forall (r :: forall a. (Functor m) => a -> m a) (f :: a -> b) (fmap :: forall a b. (Functor f) => (a -> b) -> f a -> f b).
--     (r . f) = (fmap f . r)
-- #-}

---
-- (m1)    ret a >>= k  ===  k a
m1'  :: AltMonad m => (a -> m b) -> a -> m b 
m1' k a = 
     (((joi . fmap k) . ret) a) --. Postulate -- --. R (Prop "composeAssoc")
 === ((joi . ((id (fmap k)) . ret)) a) --. R (Prop "returnFREE")
 === ((joi . (ret . k)) a)      --. QED
-}

-- {-
import ProofBase
-- import Compose (composeAssoc, composeLeftNeutral)  -- Нужно только для пруфчекенга, живет в комментариях
-- import ProofsFunctor
import GHC.Base (undefined)

import Prelude hiding ((.), id, ($), const, flip, Functor(..), Applicative(..))

------------------------------------------


class Functor f where 
  fmap :: (a -> b) -> f a -> f b

instance Functor Maybe where
  fmap _ Nothing  = Nothing     -- L (Inst "fmap")
  fmap g (Just a) = Just (g a)  -- L (Inst "fmap")

class Functor f => Applicative f where
  pure :: a -> f a
  (<*>) :: f (a -> b) -> f a -> f b
  liftA2 :: (a -> b -> c) -> f a -> f b -> f c
  liftA2 f x = (<*>) (fmap f x)

instance Applicative Maybe where
  pure = Just                   -- L (Inst "pure")
  Nothing <*> _  = Nothing      -- L (Inst "<*>")
  Just g  <*> x  = fmap g x     -- L (Inst "<*>")




f1 :: Functor f => f a -> f a
f1  =
     fmap id       --. Postulate
 === id  --. QED

f2 :: Functor f => (b -> c) -> (a -> b) ->  f a -> f c
f2 g h  =
     (fmap g . fmap h) --. Postulate
 === (fmap (g . h))    --. QED



-- ApplicativeLaws
{-
(0)
pure g <*> as = fmap g as
-}
{-
(1) identity
pure id <*> as = as
-}
{-
(2) interchange
gs <*> pure a = pure ($ a) <*> gs
Альтернативная формулировки
gs <*> pure a = fmap ($ a) gs
-}
{-
(3) homomorphism
pure g <*> pure a = pure (g a)
-}
{-
(4) composition
pure (.) <*> hs <*> gs <*> as = hs <*> (gs <*> as)
-}
a0 :: Applicative f => (a -> b) -> f a -> f b
a0 g as  =
     pure g <*> as  --. Postulate
 === fmap g as      --. QED

a1 :: Applicative f => f a -> f a
a1 as  =
     pure id <*> as  --. Postulate
 === as              --. QED

a2 :: Applicative f => f (a -> b) -> a -> f b
a2 gs a  =
     gs <*> pure a     --. Postulate
 === pure ($ a) <*> gs --. QED

a3 :: Applicative f => (a -> b) -> a -> f b
a3 g a  =
     pure (g a)   --. Postulate
 === pure g <*> pure a          --. QED

a4 :: Applicative f => f (b -> c) -> f (a -> b) -> f a -> f c
a4 hs gs as  =
     pure (.) <*> hs <*> gs <*> as   --. Postulate
 === hs <*> (gs <*> as)              --. QED


{- Это доказывается универсально из (0) закона
(1) identity
pure id <*> as = as
-}
app1Law :: Applicative f => f a -> (a -> a) -> f a
app1Law as f =
     (pure f <*> as)   --. L (Prop "a0")
 === (fmap f as)       --. QED
-- --. L (Prop "f1")
--  === id as            --. L (Def  "id")
--  === as               --. QED

-- app0LawCmps :: Applicative f => f a -> (a -> b) -> f b
-- app0LawCmps x g =
--      (pure g <*> x) --. L (Prop "a0")
--  === (fmap g x)     --. QED

app0LawCmps :: (Applicative f, Applicative g) =>  (a -> b) -> f (g a) -> f (g b)
app0LawCmps g ass  =
     (fmap (<*>) (pure (pure g)) <*> ass)     --. R (Prop "a0")
 === (pure (<*>) <*> (pure (pure g)) <*> ass) --. R (Prop "a3")
 === (pure ((<*>) (pure g)) <*> ass)          --. R Eta
 === (pure (\z -> pure g <*> z) <*> ass)      --. L (Prop "a0")
 === (pure (\z -> fmap g z) <*> ass)          --. L Eta
 === (pure (fmap g) <*> ass)                  --. L (Prop "a0")
 === (fmap (fmap g) ass)                      --. QED

-- liftA ::  Applicative f =>  (a -> b) -> f a -> f b 
-- liftA g as = pure g <*> as
 
-- liftA_f1 :: Applicative f =>  f a -> f a
-- liftA_f1 as  =
--      liftA id as     --. L (Def  "liftA")
--  === pure id <*> as  --. L (Prop "a1")
--  === as              --. QED

-- liftA_f2 :: Applicative f => (b -> c) -> (a -> b) ->  f a -> f c
-- liftA_f2 g h as =
--       (liftA g . liftA h) as                --. L (Def  ".")
--   === liftA g (liftA h as)                  --. L (Def  "liftA")
--   === liftA g (pure h <*> as)               --. L (Def  "liftA")
--   === pure g <*> (pure h <*> as)            --. R (Prop "a4")
--   === pure (.) <*> pure g <*> pure h <*> as --. R (Prop "a3")
--   === pure ((.) g) <*> pure h <*> as        --. R (Prop "a3")
--   === pure (g . h) <*> as                   --. R (Def  "liftA")
--   === liftA (g . h) as                      --. QED    

--       pure g <*> as  --. Postulate
--  === fmap g as      --. QED
-- -}

