module ProofsApplicative where

import ProofBase
-- import Compose (composeAssoc, composeLeftNeutral)  -- Нужно только для пруфчекенга, живет в комментариях
-- import ProofsFunctor
import GHC.Base (undefined)

import Prelude hiding ((.), id, ($), const, flip, Functor(..), Applicative(..))

------------------------------------------

f1 :: Functor f => f a -> f a
f1  =
     fmap id  --. Postulate
 === id       --. QED

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
a0 :: Applicative f => (a -> a) -> f a -> f a
a0 g as  =
     pure g <*> as  --. Postulate
 === fmap g as      --. QED

a1 :: Applicative f => f a -> f a
a1 as  =
     pure id <*> as  --. Postulate
 === as              --. QED

a2 :: Applicative f => f (a -> b) -> a -> f b
a2 gs a  =
     gs <*> pure a --. Postulate
 === pure ($ a) <*> gs

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
app1Law :: Applicative f => f a -> f a
app1Law as =
     pure id <*> as   --. L (Prop "a0")
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
  Nothing <*> _  = Nothing      --. L (Inst "<*>")
  Just g  <*> x  = fmap g x     --. L (Inst "<*>")

-}
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

-- pure (.) <*> u <*> v <*> w === u <*> (v <*> w)
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



---------------------------------------------------
-- Arrow
{-
instance Applicative ((->) e) where
  pure :: a -> e -> a
  pure z x = z
  
  (<*>) :: (e -> a -> b) -> (e -> a) -> e -> b
  (<*>) g h x = g x (h x)
  
  liftA2 :: (a -> b -> c) -> (e -> a) -> (e -> b) -> e -> c
  liftA2 g h1 h2 x = g (h1 x) (h2 x)
-}
instance Functor ((->) e) where
  fmap = (.)

instance Applicative ((->) e) where
  pure z x = z                   -- L (Inst "pure")
  (<*>) g h x = g x (h x)      -- L (Inst "<*>")
  liftA2 g h1 h2 x = g (h1 x) (h2 x)     -- L (Inst "<*>")

{-
(0)
pure g <*> h === fmap g h
-}
app0LawArrow :: (a -> b) -> (e -> a) -> e -> b
app0LawArrow g h =
     pure g <*> h           --. L (Inst "<*>")
 === (\x -> pure g x (h x)) --. L (Inst "pure")
 === (\x -> g (h x))        --. R (Def  ".")
 === (g . h)                --. R (Inst "fmap")
 === fmap g h               --. QED

{-
(2) interchange
g <*> pure a === pure ($ a) <*> g
-}
app2LawArrow :: (e -> a -> b) -> a -> e -> b
app2LawArrow g a =
     g <*> pure a               --. L (Inst "<*>")
 === (\x -> g x (pure a x))     --. L (Inst "pure")
 === (\x -> g x a)              --. R (Def  "$")
 === (\x -> ($) (g x) a)        --. Postulate -- {section}
 === (\x -> ($ a) (g x))        --. R (Inst "pure")
 === (\x -> pure ($ a) x (g x)) --. R (Inst "<*>")
 === pure ($ a) <*> g           --. QED


{-
(3) homomorphism
pure g <*> pure a === pure (g a)
-}
app3LawArrow :: (a -> b) -> a -> e -> b
app3LawArrow g a =
     pure g <*> pure a           --. L (Inst "<*>")
 === (\x -> pure g x (pure a x)) --. L (Inst "pure")
 === (\x -> g (pure a x))        --. L (Inst "pure")
 === (\x -> g a)                 --. R (Inst "pure")
 === pure (g a)                  --. QED

 {-
(4) composition
pure (.) <*> h <*> g <*> u === h <*> (g <*> u)
-}
app4LawArrow :: (e -> b -> c) -> (e -> a -> b) -> (e -> a) -> e -> c
app4LawArrow h g u =
     pure (.) <*> h <*> g <*> u              --. L (Inst "<*>")
 === (\x -> pure (.) x (h x)) <*> g <*> u    --. L (Inst "pure")
 === (\x -> (.) (h x)) <*> g <*> u           --. L (Inst "<*>")
 === (\y -> (\x -> (.) (h x)) y (g y)) <*> u --. L Beta
 === (\y -> (.) (h y) (g y)) <*> u           --. L (Inst "<*>")
 === (\z -> (\y -> (.) (h y) (g y)) z (u z)) --. L Beta
 === (\z -> (.) (h z) (g z) (u z))           --. L (Def  ".")
 === (\z -> h z (g z (u z)))                 --. R (Inst "<*>")
 === (\z -> h z ((g <*> u) z))               --. R (Inst "<*>")
 === h <*> (g <*> u)                         --. QED



{- CMPS
---------------------------------------------------
-- Cmps (Определен в ProofsFunctor)
-- {-
newtype Cmps f g x = Cmps (f (g x))

instance (Functor f, Functor g) => Functor (Cmps f g) where
  fmap :: (Functor f, Functor g) => (a -> b) -> Cmps f g a -> Cmps f g b
  fmap f (Cmps xss) = Cmps (fmap (fmap f) xss)

-- -}
instance (Applicative f, Applicative g) => Applicative (Cmps f g) where
  pure :: a -> Cmps f g a
  pure x = Cmps (pure (pure x))
  (<*>) :: Cmps f g (a -> b) -> Cmps f g a -> Cmps f g b
  Cmps fss <*> Cmps xss = Cmps (fmap (<*>) fss <*> xss)




{-
(0)
pure g <*> h = fmap g h
-}
app0LawCmps :: (Applicative f, Applicative g) =>  (a -> b) -> Cmps f g a -> Cmps f g b
app0LawCmps g (Cmps ass) =
     pure g <*> Cmps ass                           --. L (Inst "pure")
 === Cmps (pure (pure g)) <*> Cmps ass             --. L (Inst "<*>")
 === Cmps (fmap (<*>) (pure (pure g)) <*> ass)     --. L (Prop "a0")
 === Cmps (pure (<*>) <*> (pure (pure g)) <*> ass) --. L (Prop "a3")
 === Cmps (pure ((<*>) (pure g)) <*> ass)          --. L Eta
 === Cmps (pure (\z -> pure g <*> z) <*> ass)      --. L (Prop "a0")
 === Cmps (pure (\z -> fmap g z) <*> ass)          --. L Eta
 === Cmps (pure (fmap g) <*> ass)                  --. L (Prop "a0")
 === Cmps (fmap (fmap g) ass)                      --. L (Inst "fmap")
 === fmap g (Cmps ass)                             --. QED

{-
(2) interchange
g <*> pure a = pure ($ a) <*> g
-}
app2LawCmps :: (Applicative f, Applicative g) => Cmps f g (a -> b) -> a -> Cmps f g b
app2LawCmps (Cmps gss) a =
     Cmps gss <*> pure a                                          --. L (Inst "pure")
 === Cmps gss <*> Cmps (pure (pure a))                            --. L (Inst "<*>")
 === Cmps (fmap (<*>) gss <*> pure (pure a))                      --. L (Prop "a0")
 === Cmps (pure (<*>) <*> gss <*> pure (pure a))                  --. L (Prop "a2")
 === Cmps (pure ($ (pure a)) <*> (pure (<*>) <*> gss))            --. L (Prop "a4")
 === Cmps (pure (.) <*> pure ($ (pure a)) <*> pure (<*>) <*> gss) --. L (Prop "a3")
 === Cmps (pure ((.) ($ (pure a))) <*> pure (<*>) <*> gss)        --. L (Prop "a3")
 === Cmps (pure (((.) ($ (pure a))) (<*>)) <*> gss)               --. L (Def  ".")
 === Cmps (pure (\z -> ($ (pure a)) ((<*>) z)) <*> gss)           --. Postulate -- SECTION
 === Cmps (pure (\z -> (((<*>) z) $ (pure a))) <*> gss)           --. L (Def  "$")
 === Cmps (pure (\z -> z <*> pure a) <*> gss)                     --. L (Prop "a2")
 === Cmps (pure (\z -> pure ($ a) <*> z) <*> gss)                 --. L Eta
 === Cmps (pure ((<*>) (pure ($ a))) <*> gss)                     --. L (Prop "a3")
 === Cmps (pure (<*>) <*> pure (pure ($ a)) <*> gss)              --. L (Prop "a0")
 === Cmps (fmap (<*>) (pure (pure ($ a))) <*> gss)                --. L (Inst "<*>")
 === Cmps (pure (pure ($ a))) <*> Cmps gss                        --. L (Inst "pure")
 === pure ($ a) <*> Cmps gss                                      --. QED


{-
(3) homomorphism
pure g <*> pure a = pure (g a)
-}
app3LawCmps :: (Applicative f, Applicative g) => (a -> b) -> a -> Cmps f g b
app3LawCmps g a =
     pure g <*> pure a                                     --. L (Inst "pure")
 === Cmps (pure (pure g)) <*> pure a                       --. L (Inst "pure")
 === Cmps (pure (pure g)) <*> Cmps (pure (pure a))         --. L (Inst "<*>")
 === Cmps (fmap (<*>) (pure (pure g)) <*> pure (pure a))   --. L (Prop "a0")
 === Cmps (pure (<*>) <*> pure (pure g) <*> pure (pure a)) --. L (Prop "a3")
 === Cmps (pure ((<*>) (pure g)) <*> pure (pure a))        --. L (Prop "a3")
 === Cmps (pure ((pure g) <*> (pure a)))                   --. L (Prop "a3")
 === Cmps (pure (pure (g a)))                              --. L (Inst "pure")
 === pure (g a)                                            --. QED

 {-
(4) composition
pure (.) <*> h <*> g <*> u = h <*> (g <*> u)
-}
app4LawCmps :: (Applicative f, Applicative g) => 
    Cmps f g (b -> c) -> Cmps f g (a -> b) -> Cmps f g a -> Cmps f g c
app4LawCmps (Cmps h) (Cmps g) (Cmps u) =
     pure (.) <*> Cmps h <*> Cmps g <*> Cmps u                                                      --. L (Inst "pure")
 === Cmps (pure (pure (.))) <*> Cmps h <*> Cmps g <*> Cmps u                                        --. L (Inst "<*>")
 === Cmps (fmap (<*>) (pure (pure (.))) <*> h) <*> Cmps g <*> Cmps u                                --. L (Prop "a0")
 === Cmps (pure (<*>) <*> pure (pure (.)) <*> h) <*> Cmps g <*> Cmps u                              --. L (Inst "<*>")
 === Cmps (fmap (<*>) (pure ((<*>) (pure (.))) <*> h) <*> g)  <*> Cmps u                            --. L (Inst "<*>")
 === Cmps (fmap (<*>) (fmap (<*>) (pure ((<*>) (pure (.))) <*> h) <*> g) <*> u)                     --. L (Prop "a0")
 === Cmps (fmap (<*>) (pure (<*>) <*> (pure ((<*>) (pure (.))) <*> h) <*> g) <*> u)                 --. L (Prop "a0")
 === Cmps (pure (<*>) <*> (pure (<*>) <*> (pure ((<*>) (pure (.))) <*> h) <*> g) <*> u)             --. L (Prop "a0")
 === Cmps (pure (<*>) <*> (pure (<*>) <*> (pure ((<*>) (pure (.))) <*> h) <*> g) <*> u)             --. L (Prop "a4")
 === Cmps (pure (<*>) <*> (pure (.) <*> pure (<*>) <*> pure ((<*>) (pure (.))) <*> h <*> g) <*> u)  --. L (Prop "a3")
 === Cmps (pure (<*>) <*> (pure ((.) (<*>)) <*> pure ((<*>) (pure (.))) <*> h <*> g) <*> u)         --. L (Prop "a3")
 === Cmps (pure (<*>) <*> (pure ((.) (<*>) ((<*>) (pure (.)))) <*> h <*> g) <*> u)                  --. L (Prop "a4")
 === Cmps (pure (.) <*> pure (<*>) <*> (pure ((.) (<*>) ((<*>) (pure (.)))) <*> h) <*> g <*> u)     --. L (Prop "a3")
 === Cmps (pure ((.) (<*>)) <*> (pure ((.) (<*>) ((<*>) (pure (.)))) <*> h) <*> g <*> u)            --. L (Prop "a4")
 === Cmps (pure (.) <*> pure ((.) (<*>)) <*> pure ((.) (<*>) ((<*>) (pure (.)))) <*> h <*> g <*> u) --. L (Prop "a3")
 === Cmps (pure ((.) ((.) (<*>))) <*> pure ((.) (<*>) ((<*>) (pure (.)))) <*> h <*> g <*> u)        --. L (Prop "a3")
 === Cmps (pure ((.) ((.) (<*>)) ((.) (<*>) ((<*>) (pure (.))))) <*> h <*> g <*> u)                 --. L (Prop "lemma0")
 === Cmps (pure ((.) ($ (<*>)) ((.) (.) ((.) (.) (<*>)))) <*> h <*> g <*> u)                        --. L (Prop "a3")
 === Cmps (pure ((.) ($ (<*>))) <*> pure ((.) (.) ((.) (.) (<*>))) <*> h <*> g <*> u)               --. L (Prop "a3")
 === Cmps (pure (.) <*> pure ($ (<*>)) <*> pure ((.) (.) ((.) (.) (<*>))) <*> h <*> g <*> u)        --. L (Prop "a4")
 === Cmps (pure ($ (<*>)) <*> (pure ((.) (.) ((.) (.) (<*>))) <*> h) <*> g <*> u)                   --. L (Prop "a2")
 === Cmps (pure ((.) (.) ((.) (.) (<*>))) <*> h <*> pure (<*>) <*> g <*> u)                         --. L (Prop "a3")
 === Cmps (pure ((.) (.)) <*> pure ((.) (.) (<*>)) <*> h <*> pure (<*>) <*> g <*> u)                --. L (Prop "a0")
 === Cmps (pure (.) <*> pure (.) <*> pure ((.) (.) (<*>)) <*> h <*> pure (<*>) <*> g <*> u)         --. L (Prop "a3")
 === Cmps (pure (.) <*> (pure ((.) (.) (<*>)) <*> h) <*> pure (<*>) <*> g <*> u)                    --. L (Prop "a3")
 === Cmps (pure ((.) (.) (<*>)) <*> h <*> (pure (<*>) <*> g) <*> u)                                 --. L (Prop "a0")
 === Cmps (pure ((.) (.) (<*>)) <*> h <*> fmap (<*>) g <*> u)                                       --. L (Prop "a3")
 === Cmps (pure ((.) (.)) <*> pure (<*>) <*> h <*> fmap (<*>) g <*> u)                              --. L (Prop "a0")
 === Cmps (pure (.) <*> pure (.) <*> pure (<*>) <*> h <*> fmap (<*>) g <*> u)                       --. L (Prop "a3")
 === Cmps (pure (.) <*> (pure (<*>) <*> h) <*> fmap (<*>) g <*> u)                                  --. L (Prop "a0")
 === Cmps (pure (.) <*> fmap (<*>) h <*> fmap (<*>) g <*> u)                                        --. L (Prop "a0")
 === Cmps (pure (.) <*> fmap (<*>) h <*> fmap (<*>) g <*> u)                                        --. L (Prop "a4")
 === Cmps (fmap (<*>) h <*> (fmap (<*>) g <*> u))                                                   --. L (Inst "<*>")
 === Cmps h <*> Cmps (fmap (<*>) g <*> u)                                                           --. L (Inst "<*>")
 === Cmps h <*> (Cmps g <*> Cmps u)                                                                 --. QED

lemma0 :: Applicative f => f (b -> c) -> f (a -> b) -> f a -> f c
lemma0 hs gs as = 
     ((.) ((.) (<*>)) ((.) (<*>) ((<*>) (pure (.))))) hs gs as --. L (Def  ".")
 === ((.) (<*>) (((.) (<*>) ((<*>) (pure (.)))) hs)) gs as     --. L (Def  ".")
 === ((.) (<*>) ((<*>) (pure (.)))) hs gs <*> as               --. L (Def  ".")
 === pure (.) <*> hs <*> gs <*> as                             --. L (Prop "a4")
 === hs <*> ( gs <*> as)                                       --. R (Def  ".")
 === (.) ((<*>) hs) ((<*>) gs) as                              --. R (Def  ".")
 === (.) ((.) ((<*>) hs)) (<*>) gs as                          --. R (Def  ".")
 === (.) ((.) (.) (<*>) hs) (<*>) gs as                        --. R (Def  ".")
 === ((.) (.) ((.) (.) (<*>)) hs) (<*>) gs as                  --. R (Def  "$")
 === (($ (<*>)) ((.) (.) ((.) (.) (<*>)) hs)) gs as            --. R (Def  ".")
 === ((.) ($ (<*>)) ((.) (.) ((.) (.) (<*>)))) hs gs as        --. QED
CMPS -}

