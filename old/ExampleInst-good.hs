module ExampleInstGood where

import ProofBase
import Prelude hiding ((.), ($), id, flip, Functor(..), Applicative(..))
-- import GHC.Internal.Base hiding (Functor, Functor Maybe)


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

f1 :: Functor f => f a -> f a
f1 =
     fmap id --. Postulate
 === id         --. QED

f2 :: Functor f => (b -> c) -> (a -> b) ->  f a -> f c
f2 g h  =
     (fmap g . fmap h) --. Postulate
 === fmap (g . h)      --. QED


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
     pure g <*> pure a   --. Postulate
 === pure (g a)          --. QED

a4 :: Applicative f => f (b -> c) -> f (a -> b) -> f a -> f c
a4 hs gs as  =
     pure (.) <*> hs <*> gs <*> as   --. Postulate
 === hs <*> (gs <*> as)              --. QED


{- Это доказывается универсально из (0) закона
(1) identity
pure id <*> as = as
-}
app1Law :: Applicative f =>  f a -> f a
app1Law as =
     pure id <*> as   --. Postulate --L (Prop "a0")
 === fmap id as       --. L (Prop "f1")
 === id as            --. L (Def  "id")
 === as               --. QED

---------------------------------------------------

{-
Покажите, что liftA удовлетворяет законам функтора
-}
liftA ::  Applicative f =>  (a -> b) -> f a -> f b 
liftA g as = pure g <*> as
 
liftA_f1 :: Applicative f =>  f a -> f a
liftA_f1 as  =
     liftA id as     --. L (Def  "liftA")
 === pure id <*> as  --. L (Prop "a1")
 === as              --. QED

liftA_f2 :: Applicative f => (b -> c) -> (a -> b) ->  f a -> f c
liftA_f2 g h as =
      (liftA g . liftA h) as                --. L (Def  ".")
  === liftA g (liftA h as)                  --. L (Def  "liftA")
  === liftA g (pure h <*> as)               --. L (Def  "liftA")
  === pure g <*> (pure h <*> as)            --. R (Prop "a4")
  === pure (.) <*> pure g <*> pure h <*> as --. L (Prop "a3")
  === pure ((.) g) <*> pure h <*> as        --. L (Prop "a3")
  === pure (g . h) <*> as                   --. R (Def  "liftA")
  === liftA (g . h) as                      --. QED            
 
 
--------------------------------------------------
{-
Проверьте, что законы аппликативных функторов

-- (0)
fmap g xs  ===  pure g <*> xs
-- (1) Identity
pure id <*> v  ===  v
-- (2) Interchange
u <*> pure x  ===  pure ($ x) <*> u
-- (3) Homomorphism
pure g <*> pure x  ===  pure (g x)
-- (4) Composition
pure (.) <*> u <*> v <*> w  ===  u <*> (v <*> w)

выполняются для типа Maybe.

-----
Определения:

instance Functor Maybe where
  fmap _ Nothing  = Nothing     --. L (Inst "fmap")
  fmap g (Just a) = Just (g a)  --. L (Inst "fmap")

instance Applicative Maybe where
  pure = Just                   --. L (Inst "pure")
  Nothing <*> _  = Nothing      -- <*> (1)
  Just g  <*> x  = fmap g x     -- <*> (2)

-}



-- fmap g v  =  pure g <*> v
ap0LawMaybe :: (a -> b) -> Maybe a -> Maybe b
ap0LawMaybe g v = 
     pure g <*> v --. L (Inst "pure")
 === Just g <*> v --. L (Inst "<*>")
 === fmap g v     --. QED

-- pure id <*> v  ===  v
ap1LawMaybe :: Maybe a -> Maybe a
ap1LawMaybe v = 
     pure id <*> v --. L (Inst "pure")
 === Just id <*> v --. L (Inst "<*>")
 === fmap id v     --. L (Prop "f1")
 === id v          --. L (Def  "id")
 === v             --. QED

-- нам неоднократно потребуется лемма
lemma_JJ2J :: (a -> b) -> a -> Maybe b
lemma_JJ2J f x =
     Just f <*> Just x --. L (Inst "<*>")
 === fmap f (Just x)   --. L (Inst "fmap")
 === Just (f x)        --. QED

-- pure g <*> pure x  ===  pure (g x)
ap2LawMaybe :: (a -> b) -> a -> Maybe b
ap2LawMaybe g x = 
     pure g <*> pure x --. L (Inst "pure")
 === Just g <*> pure x --. L (Inst "pure")
 === Just g <*> Just x --. L (Prop "lemma_JJ2J")
 === Just (g x)        --. R (Inst "pure")
 === pure (g x)        --. QED

-- u <*> pure x  ===  pure ($ x) <*> u
ap3LawMaybe :: Maybe (a -> b) -> a -> Maybe b
ap3LawMaybe Nothing x = 
     pure ($ x) <*> Nothing --. L (Inst "pure")
 === Just ($ x) <*> Nothing --. L (Inst "<*>")
 === fmap ($ x) Nothing     --. L (Inst "fmap")
 === Nothing                --. R (Inst "<*>")
 === Nothing <*> pure x     --. QED

ap3LawMaybe (Just f) x = 
     pure ($ x) <*> Just f --. L (Inst "pure")
 === Just ($ x) <*> Just f --. L (Prop "lemma_JJ2J")
 === Just (($ x) f)        --. L (Def  "$")
 === Just (f x)            --. R (Prop "lemma_JJ2J")
 === Just f <*> Just x     --. R (Inst "pure")
 === Just f <*> pure x     --. QED

-- -- pure (.) <*> u <*> v <*> w === u <*> (v <*> w)
ap4LawMaybe :: Maybe (b -> c) -> Maybe (a -> b) -> Maybe a -> Maybe c
ap4LawMaybe Nothing gs zs =
     pure (.) <*> Nothing <*> gs <*> zs --. L (Inst "pure")
 === Just (.) <*> Nothing <*> gs <*> zs --. L (Inst "<*>")
 === fmap (.) Nothing <*> gs <*> zs     --. L (Inst "fmap")
 === Nothing  <*> gs <*> zs             --. L (Inst "<*>")
 === Nothing <*> zs                     --. L (Inst "<*>")
 === Nothing                            --. R (Inst "<*>")
 === Nothing <*> (gs <*> zs)            --. QED

ap4LawMaybe (Just f) (Just g) (Just z) = 
     pure (.) <*> Just f <*> Just g <*> Just z  --. L (Inst "pure")
 === Just (.) <*> Just f <*> Just g <*> Just z  --. L (Prop "lemma_JJ2J")
 === Just ((.) f)        <*> Just g <*> Just z  --. L (Prop "lemma_JJ2J")
 === Just ((.) f g)                 <*> Just z  --. L (Prop "lemma_JJ2J")
 === Just ((.) f g z)                           --. L (Def  ".")
 === Just (f (g z))                             --. R (Prop "lemma_JJ2J")
 === Just f <*> Just (g z)                      --. R (Prop "lemma_JJ2J")
 === Just f <*> (Just g <*> Just z)             --. QED


