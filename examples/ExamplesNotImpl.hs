 {-# LANGUAGE InstanceSigs #-}
module ExampleNotImpl where

import ProofBase
-- import Compose (composeAssoc, composeLeftNeutral)  -- Нужно только для пруфчекенга, живет в комментариях
-- import ProofsFunctor
-- import ProofsApplicative

import Control.Applicative (ZipList)
-- import Control.Monad.State.Lazy
-- import Data.Functor --(($>),(<$))
import Prelude hiding ((.), id, ($), const, flip, Functor(..), Applicative(..), Monad(..))

-- {- CMPS
---------------------------------------------------
-- Cmps (Определен в ProofsFunctor)
-- {-
class Functor f where 
  fmap :: (a -> b) -> f a -> f b

class Functor f => Applicative f where
  pure :: a -> f a
  (<*>) :: f (a -> b) -> f a -> f b
  liftA2 :: (a -> b -> c) -> f a -> f b -> f c
  liftA2 f x = (<*>) (fmap f x)

infixl 1 >>=

class Applicative m => Monad m where
    (>>=) :: m a -> (a -> m b) -> m b 
    return :: a -> m a

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

instance Functor ((->) e) where
  fmap  = (.)     -- L (Inst "fmap")



{-
(0)
pure g <*> h = fmap g h
-}
app0LawCmps :: (Applicative f, Applicative g) =>  (a -> b) -> Cmps f g a -> Cmps f g b
app0LawCmps g (Cmps ass) =
     pure g <*> Cmps ass                           --. L (Inst "pure")
 === Cmps (pure (pure g)) <*> Cmps ass             --. L (Inst "<*>")
 === Cmps (fmap (<*>) (pure (pure g)) <*> ass)     --. R (Prop "a0")
 === Cmps (pure (<*>) <*> (pure (pure g)) <*> ass) --. L (Prop "a3")
 === Cmps (pure ((<*>) (pure g)) <*> ass)          --. R Eta
 === Cmps (pure (\z -> pure g <*> z) <*> ass)      --. L (Prop "a0")
 === Cmps (pure (\z -> fmap g z) <*> ass)          --. L Eta
 === Cmps (pure (fmap g) <*> ass)                  --. L (Prop "a0")
 === Cmps (fmap (fmap g) ass)                      --. R (Inst "fmap")
 === fmap g (Cmps ass)                             --. QED

{-
(2) interchange
g <*> pure a = pure ($ a) <*> g
-}
--      gs <*> pure a --. Postulate
--  === pure ($ a) <*> gs
app2LawCmps :: (Applicative f, Applicative g) => Cmps f g (a -> b) -> a -> Cmps f g b
app2LawCmps (Cmps gss) a =
     Cmps gss <*> pure a                                          --. L (Inst "pure")
 === Cmps gss <*> Cmps (pure (pure a))                            --. L (Inst "<*>")
 === Cmps (fmap (<*>) gss <*> pure (pure a))                      --. R (Prop "a0")
 === Cmps (pure (<*>) <*> gss <*> pure (pure a))                  --. L (Prop "a2")
 === Cmps (pure ($ (pure a)) <*> (pure (<*>) <*> gss))            --. R (Prop "a4")
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
 === Cmps (pure (pure (g a)))                              --. R (Inst "pure")
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
-- CMPS -}







-- {- STATE
-- State

newtype State s a = State (s -> (s, a)) --{ runState :: s -> (s, a) }
runState :: State s a -> s -> (s, a)
runState (State f) a = f a

instance Functor (State s) where
  fmap :: (a -> b) -> State s a -> State s b
  fmap f (State g) = State (\s -> case g s of (s', a) -> (s', f a)) -- let (s', a) = g s in (s', f a))

--functor1LawState ::  (e -> a) -> (e -> a)
functor1LawState :: State s b -> State s b
functor1LawState (State g) =
     fmap id (State g)                               --. L (Inst "fmap")
 === State (\s -> case g s of (s', a) -> (s', id a)) --. L (Def  "id")
 === State (\s -> case g s of (s', a) -> (s', a))    --. Postulate -- UNCASE??
 === State (\s -> g s)                               --. L Eta
 === State g                                         --. QED

-- STATE -}


