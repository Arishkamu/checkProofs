 {-# LANGUAGE InstanceSigs #-}
module ProofsMonoidal where

import ProofBase
-- import Compose (composeAssoc, composeLeftNeutral)  -- Нужно только для пруфчекенга, живет в комментариях
-- import ProofsFunctor
-- import ProofsApplicative

import Control.Applicative
import  Control.Monad.State.Lazy
import Data.Functor --(($>),(<$))
import Prelude hiding ((.), id, ($), const, flip)

infixl 4 *&*
class Functor f => Monoidal f where
  unit  :: f ()                  -- оборачиваем что-то неинтересное
  (*&*) :: f a -> f b -> f (a,b) -- контейнер пар из пары контейнеров

instance Monoidal [] where
  unit :: [()]
  unit = [()]
  (*&*) :: [a] -> [b] -> [(a, b)]
  --xs *&* ys = [ (x,y) | x <- xs, y <- ys ]
  as *&* bs = concat (map (\a -> map (\b -> (a,b)) bs) as) -- Так лучше доказывать законы, если соберемся
{-
GHCi> [1,2] *&* [3,4,5]
[(1,3),(1,4),(1,5),(2,3),(2,4),(2,5)]
-}

  
instance Monoidal ZipList where
  unit :: ZipList ()
  unit = ZipList (repeat ())
  (*&*) :: ZipList a -> ZipList b -> ZipList (a, b)
  ZipList xs *&* ZipList ys = ZipList (zip xs ys)

{-
GHCi> getZipList $ ZipList [1,2] *&* ZipList [3,4,5]
[(1,3),(2,4)]
-}  

instance Monoidal Maybe where
  unit :: Maybe ()
  unit = Just ()
  (*&*) :: Maybe a -> Maybe b -> Maybe (a, b)
  Just x *&* Just y = Just (x,y)
  _      *&* _      = Nothing

{-
GHCi> Just 3 *&* Just 5
Just (3,5)
GHCi> Just 3 *&* Nothing
Nothing
-}

instance Monoidal (Either e) where
  unit :: Either e ()
  unit = Right ()
  
  (*&*) :: Either e a -> Either e b -> Either e (a,b)
  Right x *&* v = fmap ((,) x) v
  Left e  *&* _       = Left e

{-
GHCi> Right 3 *&* Right 5
Right (3,5)
GHCi> Right 3 *&* Left 'B'
Left 'B'
GHCi> Left 'A' *&* Left 'B'
Left 'A'
-}

instance Monoid w => Monoidal ((,) w) where
  unit :: (w,())
  unit = (mempty,())

  (*&*) :: (w,a) -> (w,b) -> (w,(a,b))
  (u,x) *&* (v,y) = (u `mappend` v, (x,y))

{-
GHCi> ("This is ",3) *&* ("a pair!",5)
("This is a pair!",(3,5))
-}

instance Monoidal ((->) e) where
  unit :: e -> ()
  unit = \_ -> ()

  (*&*) :: (e -> a) -> (e -> b) -> e -> (a,b)
  f *&* g = \e -> (f e, g e)

{-
GHCi> (^2) *&* (*2) $ 5
(25,10)
-}

{- BBBBBB 
instance Monoidal (State s) where
  unit :: State s ()
  unit = State $ \s -> (s,())

  (*&*) :: State s a -> State s b -> State s (a,b)
  (State ha) *&* (State hb) = State $ 
    \s -> let (s' , a) = ha s
              (s'', b) = hb s'
          in (s'', (a, b))
BBBBBBB-}

{-
ghci> testS = State (\s -> (s+1,10*s))
ghci> runState testS 6 
(7,60)
ghci> runState (testS *&* testS) 6 
(8,(60,70))
-}


--------------------------------------------------------
{-
ЗАКОНЫ Monoidal
-- (1) Left identity
snd <$> (unit *&* bs) = bs

-- (2) Right identity
fst <$> (as *&* unit) = as 

unit - "безэффектен".
-}
ml1 :: Monoidal f => f b -> f b
ml1 bs =  
     fmap snd (unit *&* bs) --. Postulate
 === bs                     --. QED

ml2 :: Monoidal f => f a -> f a
ml2 as =
     fmap fst (as *&* unit) --. Postulate
 === as                     --. QED

---------------
r2l :: (a, (b, c)) -> ((a, b), c)
r2l (x, (y, z)) = ((x, y), z)

l2r :: ((a, b), c) -> (a, (b, c))
l2r ((x, y), z) = (x, (y, z))
{-
Пара таких функций задает изоморфизм между типами (a, (b, c)) и ((a, b), c):
r2l . l2r = id :: ((a, b), c) -> ((a, b), c)
l2r . r2l = id :: (a, (b, c)) -> (a, (b, c))
-}
isoTriple ::((a,b),c) -> ((a,b),c) 
isoTriple = 
    (r2l . l2r)                                    --. Postulate -- --. R Eta
 === (\((a,b),c) -> (r2l . l2r) ((a,b),c))         --. L (Def  ".")
 === (\((a,b),c) -> (\x -> r2l (l2r x)) ((a,b),c)) --. L Beta
 === (\((a,b),c) -> r2l (l2r ((a,b),c)))           --. L (Def  "l2r")
 === (\((a,b),c) -> r2l (a,(b,c)))                 --. L (Def  "r2l")
 === (\((a,b),c) -> ((a,b),c))                     --. L (Def  "id")
 === (\((a,b),c) -> id ((a,b),c))                  --. L Eta
 === id                                            --. QED

isoTriple' :: (a,(b,c)) -> (a,(b,c)) 
isoTriple' = 
     (l2r . r2l)                                   --. Postulate ----. R Eta
 === (\(a,(b,c)) -> (l2r . r2l) (a,(b,c)))         --. L (Def  ".")
 === (\(a,(b,c)) -> (\x -> l2r (r2l x)) (a,(b,c))) --. L Beta
 === (\(a,(b,c)) -> l2r (r2l (a,(b,c))))           --. L (Def  "r2l")
 === (\(a,(b,c)) -> l2r ((a,b),c))                 --. L (Def  "l2r")
 === (\(a,(b,c)) -> (a,(b,c)))                     --. L (Def  "id")
 === (\(a,(b,c)) -> id (a,(b,c)))                  --. L Eta
 === id                                            --. QED

-- {- AAAAA

{-
-- (3) Associativity
r2l <$> (as *&* (bs *&* cs)) = (as *&* bs) *&* cs 
тип обеих частей f a -> f b -> f c ---> f ((a, b), c)
-}
ml3 :: Monoidal f => f a -> f b -> f c -> f ((a, b), c)
ml3 as bs cs =
     fmap r2l (as *&* (bs *&* cs)) --. Postulate
 === (as *&* bs) *&* cs            --. QED

ml3' :: Monoidal f => f a -> f b -> f c -> f (a, (b, c))
ml3' as bs cs =
    (as *&* (bs *&* cs))                      --. Postulate -- [f1]
 === fmap id (as *&* (bs *&* cs))             --. L (Prop "isoTriple'")
 === fmap (l2r . r2l) (as *&* (bs *&* cs))    --. Postulate -- [f2]
 === fmap l2r (fmap r2l (as *&* (bs *&* cs))) --. L (Prop "ml3")
 === fmap l2r ((as *&* bs) *&* cs)            --. QED

--------------------
(***) :: (a -> a') -> (b -> b') -> (a, b) -> (a', b')
(***) g h p = (g (fst p), h (snd p))
{-
-- (4) Naturality
(g *** h) <$> (as *&* bs) = (g <$> as) *&* (h <$> bs)  
тип обеих частей (a -> a') -> (b -> b') -> f a -> f b ---> f (a', b')
ИЛИ по-другому
-- (4) Naturality'
bimap g h <$> (as *&* bs) = (g <$> as) *&* (h <$> bs) 
ИЛИ по-другому
-- (4) Naturality''
fmap (\(x, y) -> (g x, h y)) (as *&* bs) = fmap g as *&* fmap h bs  
-}

ml4 :: Monoidal f => (a1 -> a2) -> (b1 -> b2) -> f a1 -> f b1 -> f (a2, b2)
ml4 g h as bs = 
     fmap (\(x, y) -> (g x, h y)) (as *&* bs) --. Postulate
 === fmap g as *&* fmap h bs                  --. QED
 
-- {- AAAAAAA
--------------------------------------------------------------
{-
instance Monoidal Maybe where
  unit :: Maybe ()
  unit = Just ()
  (*&*) :: Maybe a -> Maybe b -> Maybe (a, b)
  Just x *&* Just y = Just (x,y)
  _      *&* _      = Nothing
-}

{-
-- (1) Left identity
fmap snd (unit *&* bs) === bs
-}
mono1LawMaybe :: Maybe a -> Maybe a
mono1LawMaybe Nothing =  
     fmap snd (unit *&* Nothing) -- inst (*&*) (2)
 === fmap snd Nothing            -- inst fmap
 === Nothing
mono1LawMaybe (Just x) =  
     fmap snd (unit *&* Just x)    -- inst unit
 === fmap snd (Just () *&* Just x) -- inst (*&*) (1)
 === fmap snd (Just ((),x))        -- inst fmap
 === Just (snd ((),x))             -- snd
 === Just x

{-
-- (2) Right identity
fmap fst (as *&* unit) === as 
-}
mono2LawMaybe :: Maybe a -> Maybe a
mono2LawMaybe Nothing =  
     fmap fst (Nothing *&* unit) -- inst (*&*) (2)
 === fmap fst Nothing            -- inst fmap
 === Nothing
mono2LawMaybe (Just x) =  
     fmap fst (Just x *&* unit)    -- inst unit
 === fmap fst (Just x *&* Just ()) -- inst (*&*) (1)
 === fmap fst (Just (x,()))        -- inst fmap
 === Just (fst (x,()))             -- fst
 === Just x

{-
-- (3) Associativity
fmap r2l (as *&* (bs *&* cs)) ==== (as *&* bs) *&* cs 
-}
mono3LawMaybe :: Maybe a -> Maybe b -> Maybe c -> Maybe ((a, b), c)
mono3LawMaybe Nothing bs cs =
     fmap r2l (Nothing *&* (bs *&* cs)) -- inst (*&*) (2)
 === fmap r2l Nothing                   -- inst fmap
 === Nothing                            -- inst (*&*) (2)
 === Nothing *&* cs                     -- inst (*&*) (2)
 === (Nothing *&* bs) *&* cs 
mono3LawMaybe (Just a) (Just b) (Just c) =
     fmap r2l (Just a *&* (Just b *&* Just c)) -- inst (*&*) (1)
 === fmap r2l (Just a *&* Just (b,c))          -- inst (*&*) (1)
 === fmap r2l (Just (a,(b,c)))                 -- inst fmap
 ===  Just (r2l (a,(b,c)))                     -- inst r2l
 ===  Just ((a,b),c)                           -- inst (*&*) (1)
 === Just (a,b) *&* Just c                     -- inst (*&*) (1)
 === (Just a *&* Just b) *&* Just c

-------------------------------------------------------------
-- Всякий аппликативный функтор моноидален.

unit' :: Applicative f => f ()
unit' = pure ()

pair' :: Applicative f => f a -> f b -> f (a,b)
--pair' = liftA2 (,)
pair' as bs = pure (,) <*> as <*> bs  
{-
Покажите, что из аппликативных законов следуют моноидальные.
Иначе говоря покажите, что реализованные вами unit' и pair'
подчиняются законам моноидальных функторов.
-}

{-
Для справки, импортируются из ProofsApplicative 
a1 :: Applicative f => f a -> f a
a1 as  =
     pure id <*> as  --. Postulate
 === as

a2 :: Applicative f => f (a -> b) -> a -> f b
a2 gs a  =
     gs <*> pure a --. Postulate
 === pure ($ a) <*> gs

a3 :: Applicative f => (a -> b) -> a -> f b
a3 g a  =
     pure g <*> pure a   --. Postulate
 === pure (g a)

a4 :: Applicative f => f (b -> c) -> f (a -> b) -> f a -> f c
a4 hs gs as  =
     pure (.) <*> hs <*> gs <*> as   --. Postulate
 === hs <*> (gs <*> as)
-}

{-
(1) Left identity
snd <$> (unit *&* as) = as
-}
monLaw1 :: Applicative f => f b -> f b
monLaw1 as =
     fmap snd (pair' unit' as)               -- pair'
 === fmap snd (pure (,) <*> unit' <*> as)    -- unit'
 === fmap snd (pure (,) <*> pure () <*> as)  -- [a3]
 === fmap snd (pure ((,) ()) <*> as)         -- [a0]
 === fmap snd (fmap ((,) ()) as)             --. Postulate -- [f2]
 === fmap (snd . (,) ()) as                  --. L (Def  ".")
 === fmap (\x -> snd ((),x)) as              -- snd
 === fmap (\x -> x) as                       --. L (Def  "id")
 === fmap (\x -> id x) as                    --. L Eta
 === fmap id as                              --. Postulate -- [f1]
 === id as                                   --. L (Def  "id")
 === as

 {-
 (2) Right identity
fst <$> (as *&* unit) = as 
 -}
monLaw2 :: Applicative f => f b -> f b
monLaw2 as =
     fmap fst (pair' as unit')                               -- pair'
 === fmap fst (pure (,) <*> as <*> unit')                    -- unit'
 === fmap fst (pure (,) <*> as <*> pure ())                  -- [a3]
 === fmap fst (pure ($ ()) <*> (pure (,) <*> as))            -- [a4]
 === fmap fst (pure (.) <*> pure ($ ()) <*> pure (,) <*> as) -- [a2]
 === fmap fst (pure ((.) ($ ())) <*> pure (,) <*> as)        -- [a2]
 === fmap fst (pure (($ ()) . (,)) <*> as)                   -- [a0]
 === fmap fst (fmap (($ ()) . (,)) as)                       --. Postulate -- [f2]
 === fmap (fst . (($ ()) . (,))) as                          -- [lemmaML2]
 === fmap id as                                              --. Postulate -- [f1]
 === id as                                                   --. L (Def  "id")
 === as

lemmaML2 :: c -> c
lemmaML2 =
     fst . (($ ()) . (,))                   --. L (Def  ".")
 === (\x -> fst ((($ ()) . (,)) x))         --. L (Def  ".")
 === (\x -> fst ((\y -> ($ ()) ((,) y)) x)) --. L Beta
 === (\x -> fst (($ ()) ((,) x)))           -- ($) SECTION
 === (\x -> fst (x,()))                     -- fst
 === (\x -> x)                              --. L (Def  "id")
 === (\x -> id x)                           --. L Eta
 === id

{-
(3) Associativity
r2l <$> (as *&* (bs *&* cs)) = (as *&* bs) *&* cs 
для справки
r2l :: (a, (b, c)) -> ((a, b), c)
r2l (x, (y, z)) = ((x, y), z)
-}
monLaw3 :: Applicative f => f a -> f b -> f c -> f ((a, b), c)
monLaw3 as bs cs =
     fmap r2l (pair' as (pair' bs cs)) -- pair'
 === fmap r2l (pure (,) <*> as <*> (pair' bs cs)) -- pair'
 === fmap r2l (pure (,) <*> as <*> (pure (,) <*> bs <*> cs))  -- [a4]
 === fmap r2l (pure (.) <*> (pure (,) <*> as) <*> (pure (,) <*> bs) <*> cs)  -- [a4]
 === fmap r2l (pure (.) <*> pure (.) <*> pure (,) <*> as <*> (pure (,) <*> bs) <*> cs)  -- [a3]
 === fmap r2l (pure ((.) (.)) <*> pure (,) <*> as <*> (pure (,) <*> bs) <*> cs)  -- [a3]
 === fmap r2l (pure ((.) (.) (,)) <*> as <*> (pure (,) <*> bs) <*> cs)  -- [a4]
 === fmap r2l (pure (.) <*> (pure ((.) (.) (,)) <*> as) <*> pure (,) <*> bs <*> cs)  -- [a4]
 === fmap r2l (pure (.) <*> pure (.) <*> pure ((.) (.) (,)) <*> as <*> pure (,) <*> bs <*> cs)  -- [a3]
 === fmap r2l (pure ((.) (.)) <*> pure ((.) (.) (,)) <*> as <*> pure (,) <*> bs <*> cs)  -- [a3]
 === fmap r2l (pure (((.) (.)) ((.) (.) (,))) <*> as <*> pure (,) <*> bs <*> cs)  -- [a2]
 === fmap r2l (pure ($ (,)) <*> (pure (((.) (.)) ((.) (.) (,))) <*> as) <*> bs <*> cs)  -- [a4]
 === fmap r2l (pure (.) <*> pure ($ (,)) <*> pure (((.) (.)) ((.) (.) (,))) <*> as <*> bs <*> cs)  -- [a3]
 === fmap r2l (pure ((.) ($ (,))) <*> pure (((.) (.)) ((.) (.) (,))) <*> as <*> bs <*> cs)  -- [a3]
 === fmap r2l (pure (((.) ($ (,))) (((.) (.)) ((.) (.) (,)))) <*> as <*> bs <*> cs)  -- [lemmaML3']
 === fmap r2l (pure genR <*> as <*> bs <*> cs)  -- [a0]
 === pure r2l <*> (pure genR <*> as <*> bs <*> cs)  -- [a4]
 === pure (.) <*> pure r2l <*> (pure genR <*> as <*> bs) <*> cs  -- [a3]
 === pure ((.) r2l) <*> (pure genR <*> as <*> bs) <*> cs  -- [a4]
 === pure (.) <*> pure ((.) r2l) <*> (pure genR <*> as) <*> bs <*> cs  -- [a3]
 === pure ((.) ((.) r2l)) <*> (pure genR <*> as) <*> bs <*> cs  -- [a4]
 === pure (.) <*> pure ((.) ((.) r2l)) <*> pure genR <*> as <*> bs <*> cs  -- [a3]
 === pure ((.) ((.) ((.) r2l))) <*> pure genR <*> as <*> bs <*> cs  -- [a3]
 === pure ((.) ((.) ((.) r2l)) genR) <*> as <*> bs <*> cs  -- [lemmaML3''']
 === pure (\x -> \y -> \z -> ((x,y),z)) <*> as <*> bs <*> cs -- [lemmaML3'']
 === pure ((.) ((.) (,)) (,)) <*> as <*> bs <*> cs -- [a3]
 === pure ((.) ((.) (,))) <*> pure (,) <*> as <*> bs <*> cs -- [a3]
 === pure (.) <*> pure ((.) (,)) <*> pure (,) <*> as <*> bs <*> cs -- [a4]
 === pure ((.) (,)) <*> (pure (,) <*> as) <*> bs <*> cs -- [a3]
 === pure (.) <*> pure (,) <*> (pure (,) <*> as) <*> bs <*> cs -- [a4]
 === pure (,) <*> (pure (,) <*> as <*> bs) <*> cs -- pair'
 === pure (,) <*> (pair' as bs) <*> cs -- pair'
 === pair' (pair' as bs) cs 

genR :: a1 -> a2 -> a3 -> (a1, (a2, a3))
genR x y z = (x,(y,z))

lemmaML3' :: a1 -> a2 -> a3 -> (a1, (a2, a3))
lemmaML3' =
     (.) ($ (,)) (((.) (.)) ((.) (.) (,)))           --. L (Def  ".")
 === (\x -> ($ (,)) (((.) (.)) ((.) (.) (,)) x))     -- ($)
 === (\x -> ((.) (.) ((.) (.) (,)) x) (,))           --. L (Def  ".")
 === (\x -> ((\x' -> (.) ((.) (.) (,) x')) x) (,))   --. L Beta
 === (\x -> (.) ((.) (.) (,) x) (,))                 --. L (Def  ".")
 === (\x -> \y -> ((.) (.) (,) x) ((,) y))           --. L (Def  ".")
 === (\x -> \y -> ((\x' -> (.) ((,) x')) x) ((,) y)) --. L Beta
 === (\x -> \y -> (.) ((,) x) ((,) y))               --. L (Def  ".")
 === (\x -> \y -> \z -> (x, (y, z)))                 -- genR
 === (\x -> \y -> \z -> genR x y z)                  --. L Eta
 === (\x -> \y -> genR x y)                          --. L Eta
 === (\x -> genR x)                                  --. L Eta
 === genR

lemmaML3'' :: a1 -> a2 -> a3 -> ((a1, a2), a3)
lemmaML3'' = 
     (.) ((.) (,)) (,)            --. L (Def  ".")
 === (\x -> (.) (,) ((,) x))      --. L (Def  ".")
 === (\x -> \y -> (,) (x,y))      --. L Eta
 === (\x -> \y -> \z -> ((x,y),z))

lemmaML3''' :: a -> b -> c -> ((a, b), c)
lemmaML3''' = 
     (.) ((.) ((.) r2l)) genR             --. L (Def  ".")
 === (\x -> (.) ((.) r2l) (genR x))       --. L (Def  ".")
 === (\x -> \y -> (.) r2l (genR x y))     --. L (Def  ".")
 === (\x -> \y -> \z -> r2l (genR x y z)) -- genR
 === (\x -> \y -> \z -> r2l (x,(y,z)))    --. L (Def  "r2l")
 === (\x -> \y -> \z -> ((x,y),z))



--------------------------------------------------------------- 
-- Всякий моноидальный функтор аппликативен.

apP :: (b -> c, b) -> c
--apP = uncurry ($)
apP (f, x) = f x

-- (<$) :: Functor f => a -> f b -> f a
pure' :: Monoidal f => a -> f a
-- pure' x = x <$ unit 
pure' x = fmap (const x) unit 
--pure' x = fmap (\_ -> x) unit 

ap' :: Monoidal f => f (a -> b) -> f a -> f b
ap' u v = fmap apP (u *&* v)
--ap' u v = fmap (\(g,x) -> g x) (u *&* v)
--ap' gs as = uncurry ($) <$> (gs *&* as)

{-
liftA' :: Monoidal f => (a -> b) -> f a -> f b
liftA' = fmap -- :)
-}

liftA2' :: Monoidal f => (a -> b -> c) -> f a -> f b -> f c
liftA2' f u v = fmap (\(x,y) -> f x y) (u *&* v) 
--liftA2' f u v = uncurry f <$> (u *&* v) 

liftA3' :: Monoidal f => (a -> b -> c -> d) -> f a -> f b -> f c -> f d
liftA3' f u v w = fmap (\((x,y),z) -> f x y z) (u *&* v *&* w) 
--liftA3' f u v w = uncurry (uncurry f) <$> ((u *&* v) *&* w) 

-----------------
-- Проверим аппликативную законность приведенных pure' и ap'
{-
uncurry ($) ((f *** g) p)  =  f (fst p) (g (snd p))
-}

-- apP ((g *** h) p) = g (fst p) (h (snd p))
lem0 :: (c -> b -> d) -> (a -> b) -> (c, a) -> d
lem0 g h p  = 
     apP ((g *** h) p)           -- (***)
 === apP (g (fst p), h (snd p))  -- apP
 === g (fst p) (h (snd p))

{-
-- h = id в lem0
apP . (g *** id)  ==  uncurry g
-}
lem0' :: (a -> b -> c) -> (a, b) -> c
lem0' g  = 
     apP . (g *** id)                --. L (Def  ".")
 === (\p -> apP ((g *** id) p))      -- [lem0]
 === (\p -> g (fst p) (id (snd p)))  --. L (Def  "id")
 === (\p -> g (fst p) (snd p))       -- uncurry
 === (\p -> uncurry g p)             --. L Eta
 === uncurry g 

{-
-- g = id в lem0
apP . (id *** h)  ==  uncurry (. h)
-}
lem0'' :: (a -> b) -> (b -> c, a) -> c
lem0'' g  = 
     apP . (id *** g)                      --. L (Def  ".")
 === (\p -> apP ((id *** g) p))            -- [lem0]
 === (\p -> id (fst p) (g (snd p)))        --. L (Def  "id")
 === (\p -> (fst p) (g (snd p)))           --. L (Def  ".")
 === (\p -> (fst p . g) (snd p))           -- {section}
 === (\p -> (. g) (fst p) (snd p))         -- uncurry
 === (\p -> uncurry (. g) p)               --. L Eta
 === uncurry (. g)

{-
ap' (g <$> as) bs  ==  uncurry g <$> (as *&* bs)
-}
lem1 :: Monoidal f => (a -> b -> c) -> f a -> f b -> f c
lem1 g as bs  = 
     ap' (fmap g as) bs                     -- ap'
 === fmap apP (fmap g as *&* bs)            --. Postulate -- [f1]
 === fmap apP (fmap g as *&* fmap id bs)    -- [ml4]
 === fmap apP (fmap (g *** id) (as *&* bs)) --. Postulate -- [f2]
 === fmap (apP . (g *** id)) (as *&* bs)    -- [lem0']
 === fmap (uncurry g) (as *&* bs)
{-
ap' hs (g <$> as) == uncurry (. g) <$> (hs *&* as)
-}
lem2 :: Monoidal f => (a -> b) -> f (b -> c) -> f a -> f c
lem2 g hs as  = 
     ap' hs (fmap g as)                     -- ap'
 === fmap apP (hs *&* fmap g as)            --. Postulate -- [f1]
 === fmap apP (fmap id hs *&* fmap g as)    -- [ml4]
 === fmap apP (fmap (id *** g) (hs *&* as)) --. Postulate -- [f2]
 === fmap (apP . (id *** g)) (hs *&* as)    -- [lem0'']
  === fmap (uncurry (. g)) (hs *&* as)

{-
(0')
pure g <*> as = g <$> as
-}

{-
Лемма 1
uncurry (const g) == g . snd
-}
lemmaAL0 :: (b -> c) -> (a,b) -> c
lemmaAL0 g  = 
     uncurry (const g)                --. L Eta
 === (\p -> uncurry (const g) p)      -- uncurry
 === (\p -> const g (fst p) (snd p))  -- const
 === (\p -> g (snd p))                --. L (Def  ".")
 === g . snd

appLaw0 :: Monoidal f => (a -> b) -> f a -> f b
appLaw0 g as = 
     ap' (pure' g) as                       -- pure'
 === ap' (fmap (const g) unit) as           -- [lem1]
 === fmap (uncurry (const g)) (unit *&* as) -- [lemmaAL0]
 === fmap (g . snd) (unit *&* as)           --. Postulate -- [f2]
 === fmap g (fmap snd (unit *&* as))        -- [ml1]
 === fmap g as

{-
(1') identity
pure id <*> as = as
-}
appLaw1' :: Monoidal f => f a -> f a
appLaw1' as = 
     ap' (pure' id) as  -- [appLaw0]
 === fmap id as          --. Postulate -- [f1]
 === as 

{-
(2') interchange
gs <*> pure a = pure ($ a) <*> gs
Альтернативная формулировки
gs <*> pure a = ($ a) <$> gs
-}

{-
(Лемма 2
uncurry ($) . (id *** const a) = ($ a) . fst
)
-}
lemmaAL2 :: p -> (p -> c, b) -> c
lemmaAL2 a = 
     uncurry (. const a)                       --. L Eta
 === uncurry (\f -> (. const a) f)             -- {section}
 === uncurry (\f -> f . const a)               --. L (Def  ".")
 === uncurry (\f -> \x -> f (const a x))       -- const
 === uncurry (\f -> \x -> f a)                 --. L Eta
 === (\p -> uncurry (\f -> \x -> f a) p)       -- uncurry
 === (\p -> (\f -> \x -> f a) (fst p) (snd p)) --. L Beta
 === (\p -> (\x -> fst p a) (snd p))           --. L Beta
 === (\p -> fst p a)                           -- ($)
 === (\p -> ($) (fst p) a)                     -- {section}
 === (\p -> ($ a) (fst p))                     -- def (.)
 === ($ a) . fst 

appLaw2 :: Monoidal f => f (a -> b) -> a -> f b
appLaw2 gs a = 
     ap' gs (pure' a)                         -- pure'
 === ap' gs (fmap (const a) unit)             -- [lem2] 
 === fmap (uncurry (. const a)) (gs *&* unit) -- [lemmaAL2]
 === fmap (($ a) . fst) (gs *&* unit)         --. Postulate -- [f2]
 === fmap ($ a) (fmap fst (gs *&* unit))      -- [ml2]
 === fmap ($ a) gs                            -- [a0]
 === ap' (pure' ($ a)) gs


{-
(3') homomorphism
pure g <*> pure a = pure (g a)
-}
{-
Лемма 3
g . const a = const (g a)
-}
lemmaAL3 :: (a -> b) -> a -> x -> b
lemmaAL3 g a  = 
    g . const a            --. L (Def  ".")
 === (\x -> g (const a x)) -- const
 === (\x -> g a)           -- const
 === (\x -> const (g a) x) --. L Eta
 === const (g a)
 
appLaw3 :: Monoidal f => (a -> b) -> a -> f b
appLaw3 g a = 
     ap' (pure' g)  (pure' a)     -- [a0]
 === fmap g (pure' a)             -- pure'
 === fmap g (fmap (const a) unit) --. Postulate -- [f2]
 === fmap (g . const a) unit      -- [lemmaAL3]
 === fmap (const (g a)) unit      -- pure'
 === pure' (g a) 


{-
(4') composition
pure (.) <*> u <*> v <*> w = u <*> (v <*> w)
-}
{- L-LEMMA
uncurry (uncurry (.))  =  \((g,h),a) -> g (h a)
-}
lLemma :: ((b -> c, a -> b), a) -> c
lLemma =
    uncurry (uncurry (.))                            --. L Eta, typed
 === (\((g,h),a) -> uncurry (uncurry (.)) ((g,h),a)) -- uncurry
 === (\((g,h),a) -> uncurry (.) (g,h) a)             -- uncurry
 === (\((g,h),a) ->  (.) g h a)                      --. L (Def  ".")
 === \((g,h),a) -> g (h a)
{- R-LEMMA
uncurry (. uncurry ($)) . l2r  =  \((g,h),a) -> g (h a)
-}
rLemma :: ((b -> c, a -> b), a) -> c
rLemma =
     uncurry (. apP) . l2r                                     --. L Eta, typed
 === (\((g,h),a) -> (uncurry (. apP) . l2r) ((g,h),a))         --. L (Def  ".")
 === (\((g,h),a) -> (\x -> uncurry (. apP) (l2r x)) ((g,h),a)) --. L Beta
 === (\((g,h),a) -> uncurry (. apP) (l2r ((g,h),a)))           --. L (Def  "l2r")
 === (\((g,h),a) -> uncurry (. apP) (g,(h,a)))                 -- uncurry
 === (\((g,h),a) -> (. apP) g (h,a))                           -- {section}
 === (\((g,h),a) -> (g . apP) (h,a))                           --. L (Def  ".")
 === (\((g,h),a) -> g (apP (h,a)))                             -- apP
 === \((g,h),a) -> g (h a)
{- RL-LEMMA
uncurry (uncurry (.))  =  uncurry (. uncurry ($)) . l2r
-}
lrLemma :: ((b -> c, a -> b), a) -> c
lrLemma = 
     uncurry (uncurry (.))          -- [lLemma]
 === (\((g,h),a) -> g (h a))        -- [rLemma]
 === uncurry (. apP) . l2r


appLaw4' :: Monoidal f => f (b -> c) -> f (a -> b) -> f a -> f c
appLaw4' gs hs as =
     ap' (ap' (ap' (pure' (.)) gs) hs) as                   -- [a0]
 === ap' (ap' (fmap (.) gs) hs) as                          -- [lem1]
 === ap' (fmap (uncurry (.)) (gs *&* hs)) as                -- [lem1]
 === fmap (uncurry (uncurry (.))) ((gs *&* hs) *&* as)      -- [lrLemma] 
 === fmap (uncurry (. apP) . l2r) ((gs *&* hs) *&* as)      --. Postulate -- [f2]
 === fmap (uncurry (. apP)) (fmap l2r ((gs *&* hs) *&* as)) -- [ml3']
 === fmap (uncurry (. apP)) (gs *&* (hs *&* as))            -- [lem2]
 === ap' gs (fmap apP (hs *&* as))                          -- ap'
 ===ap' gs (ap' hs as)

-- AAAAAA-}

