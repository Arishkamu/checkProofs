module Compose where

import ProofBase

import Prelude hiding ((.), id, ($), const, flip, Functor(..), Applicative(..), Monad(..))

{-
Композиция (.) является моноидом с id в качестве нейтрального элемента

GHC.Internal.Base
Композиция определена как функция двух аргументов, поэтому она инлайнится на двух аргументах!!
{-# INLINE (.) #-}
-}
{-
(.)    :: (b -> c) -> (a -> b) -> a -> c
(.) f g = \x -> f (g x)

id                      :: a -> a
id x                    =  x

-- Доллар тоже функция одного аргумента!
-- {-# INLINE ($) #-}
($) :: forall repa repb (a :: TYPE repa) (b :: TYPE repb). (a -> b) -> a -> b
($) f = f

const                   :: a -> b -> a
const x _               =  x

flip :: forall repc a b (c :: TYPE repc). (a -> b -> c) -> b -> a -> c
flip f x y              =  f y x
-}

composeAssoc :: (c -> d) -> (b -> c) -> (a -> b) -> a -> d
composeAssoc f g h = 
     (f . (g . h))                   --. L (Def  ".")
 === (\x -> f ((g . h) x))           --. L (Def  ".")
 === (\x -> f ((\x' -> g (h x')) x)) --. L Beta 
 === (\x -> f (g (h x)))             --. L Beta 
 === (\x -> (\x' -> f (g x')) (h x)) --. R (Def  ".")
 === (\x -> (f . g) (h x))           --. R (Def  ".")
 === ((f . g) . h)                   --. QED

composeLeftNeutral :: (a -> b) -> a -> b
composeLeftNeutral f =
     (id . f)          --. L (Def  ".")
 === (\x -> id (f x))  --. L (Def  "id")
 === (\x -> f x)       --. L Eta
 === f                 --. QED

composeRightNeutral :: (a -> b) -> a -> b
composeRightNeutral f =
     (f . id)          --. L (Def  ".")
 === (\x -> f (id x))  --. L (Def  "id")
 === (\x -> f x)       --. L Eta
 === f                 --. QED

{-
несколько версий, иллюстрирующих разные  (по степени бесточечности) способы записи одной и той же теоремы
-}
{- flip . flip === id -}
flipFlipIsId :: (a -> b -> c) -> a -> b -> c
flipFlipIsId  = 
     (flip . flip)                         --. L (Def  ".") 
 === (\f -> flip (flip f))                 --. R Eta
 === (\f -> \x -> flip (flip f) x)         --. R Eta
 === (\f -> \x -> \y -> flip (flip f) x y) --. L (Def  "flip")
 === (\f -> \x -> \y -> flip f y x)        --. L (Def  "flip")
 === (\f -> \x -> \y -> f x y)             --. L Eta
 === (\f -> \x -> f x)                     --. L Eta
 === (\f -> f)                             --. R (Def  "id")
 === (\f -> id f)                          --. L Eta
 === id                                    --. QED

{- forall f x y. flip (flip f) x y === f x y -}
flipFlipIsId' :: (a -> b -> c) -> a -> b -> c
flipFlipIsId' f x y  = 
     flip (flip f) x y  --. L (Def  "flip")
 === flip f y x         --. L (Def  "flip")
 === f x y              --. QED









 ---------------------------------------------------
-- FunctorLaws

{-
fmap id = id   -- (1 Functor Law)

fmap g . fmap h = fmap (g . h)
-}
class Functor f where 
  fmap :: (a -> b) -> f a -> f b

f1 :: Functor f => f a -> f a
f1  =
     fmap id  --. Postulate
 === id       --. QED

f2 :: Functor f => (b -> c) -> (a -> b) ->  f a -> f c
f2 g h  =
     (fmap g . fmap h) --. Postulate
 === (fmap (g . h))    --. QED


 {-
 Докажите, что второй закон функтора следует из первого, используя свободную теорему для произвольной fm :: (a -> b) -> f a -> f b

g . h = h' . g'  => fmap g . fm h = fm h' . fmap g'

Полагая  h' = id  и  g' = g . h , обнаруживаем, что посылка выполнена

g . h = id . (g . h)

откуда 

fmap g . fm h = fm id . fmap (g . h)
 
 -}

fmapFREE :: Functor f => (forall a b. (a -> b) -> f a -> f b) 
              -> (b -> c) -> (a -> b) -> f a -> f c
fmapFREE fm g h = 
    (fmap g . fm h)          --. Postulate
 === (fm id . fmap (g . h))  --. QED

f2fromf1 :: Functor f => (b -> c) -> (a -> b) -> f a -> f c
f2fromf1 g h =
     (fmap g . fmap h)               --. L (Prop "fmapFREE")
 === (fmap id . fmap (g . h))        --. L (Prop "f1")
 === (id . fmap (g . h))             --. L (Def  ".")
 === (\xs -> id (fmap (g . h) xs))   --. L (Def  "id")
 === (\xs -> fmap (g . h) xs)        --. L Eta
 === (fmap (g . h))                  --. QED
 
-------------------------------------------------------
instance Functor Maybe where
  fmap _ Nothing  = Nothing     -- L (Inst "fmap")
  fmap g (Just a) = Just (g a)  -- L (Inst "fmap")


-- Maybe
functor1LawMaybe :: Maybe a -> Maybe a
functor1LawMaybe Nothing =  
     fmap id Nothing  --. L (Inst "fmap")
 === Nothing          --. QED
functor1LawMaybe (Just a) =
     fmap id (Just a) --. L (Inst "fmap")
 === Just (id a)      --. L (Def  "id")
 === Just a           --. QED

functor2LawMaybe :: (b -> c) -> (a -> b) -> Maybe a -> Maybe c
functor2LawMaybe g h Nothing =
     ((fmap g . fmap h) Nothing) --. L (Def  ".")
 === fmap g (fmap h Nothing)     --. L (Inst "fmap")
 === fmap g Nothing              --. L (Inst "fmap")
 === Nothing                     --. R (Inst "fmap")
 === (fmap (g . h) Nothing)      --. QED
functor2LawMaybe g h (Just a) =
     (fmap g . fmap h) (Just a) --. L (Def  ".")
 === fmap g (fmap h (Just a))   --. L (Inst "fmap")
 === fmap g (Just (h a))        --. L (Inst "fmap")
 === Just (g (h a))             --. R (Def  ".")
 === Just ((g . h) a)           --. R (Inst "fmap")
 === fmap (g . h) (Just a)      --. QED



instance Functor [] where
  fmap _ []  = []     -- L (Inst "fmap")
  fmap g (x:xs) = (g x) : fmap g xs -- L (Inst "fmap")

 -- List
functor1LawList :: [a] -> [a]
functor1LawList [] =
     fmap id []  --. L (Inst "fmap")
 === []          --. QED
functor1LawList (x:xs) =
     fmap id  (x:xs)       --. L (Inst "fmap")
 === (id x : (fmap id xs)) --. L (Def  "id")
 === (x : fmap id xs)      --. Postulate -- (IH)
 === (x : xs)              --. QED

functor2LawList :: (b -> c) -> (a -> b) -> [a] -> [c]
functor2LawList g h [] =
     (fmap g . fmap h) []  --. L (Def  ".")
 === fmap g (fmap h [])   --. L (Inst "fmap")
 === fmap g []            --. L (Inst "fmap")
 === []                   --. R (Inst "fmap")
 === fmap (g . h) []      --. QED
functor2LawList g h (x:xs) =
     (fmap g . fmap h) (x:xs)         --. L (Def  ".")
 === fmap g (fmap h (x:xs))           --. L (Inst "fmap")
 === fmap g ((h x) : (fmap h xs))     --. L (Inst "fmap")
 === (g (h x) : (fmap g (fmap h xs))) --. R (Def  ".")
 === (g (h x) : (fmap g . fmap h) xs) --. Postulate -- (IH)
 === (g (h x) : (fmap (g . h) xs))    --. R (Def  ".")
 === ((g . h) x : (fmap (g . h) xs))  --. R (Inst "fmap")
 === fmap (g . h) (x:xs)              --. QED

-- {- BLOCK EITHER
instance Functor (Either a) where
  fmap _ (Left a)  = Left  a     -- L (Inst "fmap")
  fmap g (Right a) = Right (g a)  -- L (Inst "fmap")


functor1LawEither :: Either e a -> Either e a
functor1LawEither (Left e) =
     fmap id (Left e)  --. L (Inst "fmap")
 === Left e            --. QED
functor1LawEither (Right a) =
     fmap id (Right a) --. L (Inst "fmap")
 === Right (id a)      --. L (Def  "id")
 === Right a           --. QED

functor2LawEither :: (b -> c) -> (a -> b) -> Either e a -> Either e c
functor2LawEither g h (Left e) =
     (fmap g . fmap h) (Left e)  --. L (Def  ".")
 === fmap g (fmap h (Left e))    --. L (Inst "fmap")
 === fmap g (Left e)             --. L (Inst "fmap")
 === Left e                      --. R (Inst "fmap")
 === fmap (g . h) (Left e)       --. QED
functor2LawEither g h (Right a) =
     (fmap g . fmap h) (Right a) --. L (Def  ".")
 === fmap g (fmap h (Right a))   --. L (Inst "fmap")
 === fmap g (Right (h a))        --. L (Inst "fmap")
 === Right (g (h a))             --. R (Def  ".")
 === Right ((g . h) a)           --. R (Inst "fmap")
 === fmap (g . h) (Right a)      --. QED
-- BLOCK EITHER -}


-- {- BLOCK Pair
instance Functor ((,) a) where
  fmap g (a, b)  = (a, g b)     -- L (Inst "fmap")

functor1LawPair ::  (s, a) -> (s, a)
functor1LawPair (s, a) =
     fmap id (s, a) --. L (Inst "fmap")
 === (s, id a)      --. L (Def  "id")
 === (s, a)         --. QED

functor2LawPair :: (b -> c) -> (a -> b) -> (s, a) -> (s, c)
functor2LawPair g h (s, a) =
     (fmap g . fmap h) (s, a) --. L (Def  ".")
 === fmap g (fmap h (s, a))   --. L (Inst "fmap")
 === fmap g (s, (h a))        --. L (Inst "fmap")
 === (s, g (h a))             --. R (Def  ".")
 === (s, (g . h) a)           --. R (Inst "fmap")
 === fmap (g . h) (s, a)      --. QED
-- BLOCK PAIR -}

 -- Arrow
instance Functor ((->) e) where
  fmap  = (.)     -- L (Inst "fmap")

functor1LawArrow ::  (e -> a) -> (e -> a)
functor1LawArrow f =
     fmap id f          --. L (Inst "fmap")
 === (id . f)           --. L (Def  ".")
 === (\x -> id (f x))   --. L (Def  "id")
 === (\x -> f x)        --. L Eta
 === f                  --. QED

functor2LawArrow :: (b -> c) -> (a -> b) -> (e -> a) -> (e -> c)
functor2LawArrow g h f =
     (fmap g . fmap h) f   --. L (Def  ".")
 === fmap g (fmap h f)     --. L (Inst "fmap")
 === fmap g (h . f)        --. L (Inst "fmap")
 === (g . (h . f))         --. L (Prop "composeAssoc")
 === ((g . h) . f)         --. R (Inst "fmap")
 === fmap (g . h) f        --. QED


-- {- BLOCK CMPS
newtype Cmps f g x = Cmps (f (g x))  deriving (Eq, Show)
getCmps :: Cmps f g x -> f (g x)
getCmps (Cmps x) = x

instance (Functor f, Functor g) => Functor (Cmps f g) where
  fmap :: (Functor f, Functor g) => (a -> b) -> Cmps f g a -> Cmps f g b
  fmap f (Cmps xss) = Cmps (fmap (fmap f) xss)

functor1LawCmps :: (Functor f, Functor g) => Cmps f g b -> Cmps f g b
functor1LawCmps (Cmps xss) =
      fmap id (Cmps xss)         --. L (Inst "fmap")
  === Cmps (fmap (fmap id) xss)  --. L (Prop "f1")
  === Cmps (fmap id xss)         --. L (Prop "f1")
  === Cmps (id xss)              --. L (Def  "id")
  === Cmps xss                   --. QED

functor2LawCmps ::  (Functor f, Functor g) => (b -> c) -> (a -> b) -> Cmps f g a -> Cmps f g c
functor2LawCmps h1 h2 (Cmps xss) =
      (fmap h1 . fmap h2) (Cmps xss)               --. L (Def  ".")
  === fmap h1 (fmap h2 (Cmps xss))                 --. L (Inst "fmap")
  === fmap h1 (Cmps (fmap (fmap h2) xss))          --. L (Inst "fmap")
  === Cmps (fmap (fmap h1) (fmap (fmap h2) xss))   --. R (Def  ".")
  === Cmps ((fmap (fmap h1) . fmap (fmap h2)) xss) --. L (Prop "f2")
  === Cmps (fmap (fmap h1 . fmap h2) xss)          --. L (Prop "f2")
  === Cmps (fmap (fmap (h1 . h2)) xss)             --. R (Inst "fmap")
  === fmap (h1 . h2) (Cmps xss)                    --. QED
-- BLOCK CMPS -}


-- {- BLOCK STATE
    -- State

newtype State s a = State (s -> (s, a)) --{ runState :: s -> (s, a) }
runState :: State s a -> s -> (s, a)
runState (State f) a = f a

instance Functor (State s) where
  fmap :: (a -> b) -> State s a -> State s b
  fmap f (State g) = State (\s -> case g s of (s', a) -> (s', f a)) -- let (s', a) = g s in (s', f a))

{- BLOCK STATE F1L
    --functor1LawState ::  (e -> a) -> (e -> a)
    functor1LawState :: State s b -> State s b
    functor1LawState (State g) =
        fmap id (State g)                               --. L (Inst "fmap")
    === State (\s -> case g s of (s', a) -> (s', id a)) --. L (Def  "id")
    === State (\s -> case g s of (s', a) -> (s', a))    --. Postulate -- UNCASE??
    === State (\s -> g s)                               --. L Eta
    === State g                                         --. QED
BLOCK STATE F1L -}

functor2LawState :: (b -> c) -> (a -> b) -> (e -> a) -> (e -> c)
functor2LawState g h f =
      (fmap g . fmap h) f   --. L (Def  ".")
  === fmap g (fmap h f)     --. L (Inst "fmap")
  === fmap g (h . f)        --. L (Inst "fmap")
  === (g . (h . f))         --. Postulate --L (Def  ".")
  === ((g . h) . f)         --. R (Inst "fmap")
  === fmap (g . h) f        --. QED
-- BLOCK STATE -}










-----------------------------------
-- Aplicative
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



{- APPLICATIVE CMPS
    ---------------------------------------------------
    -- Cmps (Определен в ProofsFunctor)
    {-
    newtype Cmps f g x = Cmps (f (g x))

    instance (Functor f, Functor g) => Functor (Cmps f g) where
    fmap :: (Functor f, Functor g) => (a -> b) -> Cmps f g a -> Cmps f g b
    fmap f (Cmps xss) = Cmps (fmap (fmap f) xss)

    -}
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

APPLICATIVE CMPS -}









-------------------------------
-- ProofsMonad

infixl 1 >>=

class Applicative m => Monad m where
    (>>=) :: m a -> (a -> m b) -> m b 
    return :: a -> m a

-- MonadLaws
{-
return a >>= k  ===  k a                     -- 1 Monad Law
m >>= return    ===  m                       -- 2 Monad Law
m >>= k >>= k'  ===  m >>= \x -> k x >>= k'  -- 3 Monad Law
-}
-- postulates (это не доказывается, а является частью определения монады)
m1 :: Monad m => a -> (a -> m b) -> m b
m1 a k =
     (return a >>= k) --. Postulate
 === k a              --. QED

m2 :: Monad m => m a -> m a
m2 m =
     (m >>= return)    --. Postulate
 === m                 --. QED

m3 :: Monad m => m a -> (a -> m b) -> (b -> m c) -> m c
m3 m k k' =
     (m >>= k >>= k')         --. Postulate
 === (m >>= \x -> k x >>= k') --. QED

{-
Покажите, что каждая монада - это функтор. 
Для этого выразите fmap через (>>=) и return:
-}
liftM :: Monad m => (a -> b) -> m a -> m b
liftM f m  =  m >>= return . f
--liftM f xs  =  xs >>= \x -> return (f x)
-- Control.Monad.liftM
{-
Для полноценного доказательства следует еще проверить выполнение законов класса Functor.
-}
{-
1 Functor law
forall xs. liftM id m == m
-}
theoremFunctor1 :: Monad m => m b -> m b
theoremFunctor1 m =
      liftM id m                    --. L (Def  "liftM")
  === (m >>= return . id)           --. L (Def  ".")
  === (m >>= \x -> return (id x))   --. L (Def  "id")
  === (m >>= \x -> return x)        --. L Eta
  === (m >>= return)                --. L (Prop "m2")
  === m                             --. QED
{-
2 Functor law
forall f g m. liftM (f . g) m == liftM f (liftM g m)
-}
theoremFunctor2 :: Monad m => (b -> c) -> (a -> b) -> m a -> m c
theoremFunctor2 f g m =
      liftM f (liftM g m)                           --. L (Def  "liftM")
  === liftM f (m >>= return . g)                    --. L (Def  "liftM")
  === ((m >>= return . g) >>= return . f)           --. L (Prop "m3")
  === (m >>= \x -> (return . g) x >>= return . f)   --. L (Def  ".")
  === (m >>= \x -> return (g x) >>= return . f)     --. L (Prop "m1")
  === (m >>= \x -> (return . f) (g x))              --. R (Def  ".")
  === (m >>= \x -> ((return . f) . g) x)            --. L Eta
  === (m >>= (return . f) . g)                      --. R (Prop "composeAssoc") -- [Compose.composeAssoc]
  === (m >>= return . (f . g))                      --. R (Def  "liftM")
  === (liftM (f . g) m)                             --. QED


-----------------------------------------------------------------------------------
{-
Покажите, что каждая монада --- это аппликативный функтор. 
Для этого выразите (<*>) :: Applicative f => f (a -> b) -> f a -> f b
на языке монад:
-}
(<*>..) :: Monad m => m (a -> b) -> m a -> m b
fs <*>.. xs = fs >>= \f -> liftM f xs -- см. liftM выше
{-
Для полноценного доказательства следует еще проверить выполнение законов класса Applicative.
-}
{-
0 Applicative law
forall g xs. liftM g xs == return g <*>.. xs
-}
theoremApplicative0 :: Monad m => (a -> b) -> m a -> m b
theoremApplicative0 g xs =
      return g <*>.. xs                --. L (Def  "<*>..")
  === (return g >>= \f -> liftM f xs)  --. L (Prop "m1")
  === (\f -> liftM f xs) g             --. L Beta
  === liftM g xs                       --. QED

{-
1 Applicative law (Identity)
forall xs. return id <*>.. xs  == xs
-}
theoremApplicative1 :: Monad m => m b -> m b
theoremApplicative1 xs =
      return id <*>.. xs                 --. L (Def  "<*>..")
  === (return id >>= \f -> liftM f xs)   --. L (Prop "m1")
  === (\f -> liftM f xs) id              --. L Beta
  === liftM id xs                        --. L (Prop "theoremFunctor1")
  === xs                                 --. QED

{-
2 Applicative law (Homomorphism)
forall g x. return g <*>.. return x == return (g x)
-}
theoremApplicative2 :: Monad m => (a -> b) ->  a -> m b
theoremApplicative2 g x =
      return g <*>.. return x                  --. L (Def  "<*>..")
  === (return g >>= \f -> liftM f (return x))  --. L (Prop "m1")
  === (\f -> liftM f (return x)) g             --. L Beta
  === liftM g (return x)                       --. L (Def  "liftM")
  === (return x >>= return . g)                --. L (Prop "m1")
  === (return . g) x                           --. L (Def  ".")
  === return (g x)                             --. QED


{-
3 Applicative law (Interchange)
forall fs x. fs <*>.. return x  ===  return ($ x) <*>.. fs
-}
theoremApplicative3 :: Monad m => m (a -> b) -> a -> m b
theoremApplicative3 fs x =
      (fs <*>.. return x)           --. L (Prop "lemma1_tha3")
  === (fs >>= \f -> return (f x))   --. R (Prop "lemma2_tha3")
  === (return ($ x) <*>.. fs)       --. QED

lemma1_tha3 :: Monad m => m (a -> b) -> a -> m b
lemma1_tha3 fs x = -- left hand side transformation
        (fs <*>.. return x)                       --. L (Def  "<*>..")
    === (fs >>= \f -> liftM f (return x))         --. L (Def  "liftM")
    === (fs >>= \f -> return x >>= return . f)    --. L (Prop "m1")
    === (fs >>= \f -> (return . f) x)             --. L (Def  ".")
    === (fs >>= \f -> return (f x))               --. QED

lemma2_tha3 :: Monad m => m (a -> b) -> a -> m b
lemma2_tha3 fs x = -- right hand side transformation
        (return ($ x) <*>.. fs)               --. L (Def  "<*>..")
    === (return ($ x) >>= \f -> liftM f fs)   --. L (Prop "m1")
    === (\f -> liftM f fs) ($ x)              --. L Beta
    === (liftM ($ x) fs)                      --. L (Def  "liftM")
    === (fs >>= return . ($ x))               --. L (Def  ".")
    === (fs >>= \f -> return (($ x) f))       --. L (Def  "$")
    === (fs >>= \f -> return (f x))           --. QED
{-
4 Applicative law (Composition)
forall us vs xs. return (.) <*>.. us <*>.. vs <*>.. xs  ==  us <*>.. (vs <*>.. xs)
-}
theoremApplicative4 :: Monad m => m (b -> c) -> m (a -> b) -> m a -> m c
theoremApplicative4 us vs xs =
      (return (.) <*>.. us <*>.. vs <*>.. xs)      --. L (Prop "lemma1_tha4")
  === (us >>= \u -> vs >>= \v -> liftM (u . v) xs) --. R (Prop "lemma2_tha4")
  === (us <*>.. (vs <*>.. xs))                     --. QED

lemma1_tha4 :: Monad m => m (b -> c) -> m (a -> b) -> m a -> m c
lemma1_tha4 us vs xs = -- left hand side transformation
        (return (.) <*>.. us <*>.. vs <*>.. xs)                              --. L (Def  "<*>..")
    === ((return (.) >>= \c -> liftM c us) <*>.. vs <*>.. xs)                --. L (Prop "m1")
    === ((\c -> liftM c us) (.) <*>.. vs <*>.. xs)                           --. L Beta
    === (liftM (.) us <*>.. vs <*>.. xs)                                     --. L (Def  "liftM")
    === ((us >>= return . (.)) <*>.. vs <*>.. xs)                            --. L (Def  "<*>..")
    === (((us >>= return . (.)) >>= \r -> liftM r vs) <*>.. xs)              --. L (Prop "m3") 
    === ((us >>= \u -> (return . (.)) u >>= \r -> liftM r vs) <*>.. xs)      --. L (Def  ".")
    === ((us >>= \u -> return (u .) >>= \r -> liftM r vs) <*>.. xs)          --. L (Prop "m1")
    === ((us >>= \u -> (\r -> liftM r vs) (u .)) <*>.. xs)                   --. L Beta
    === ((us >>= \u -> liftM (u .) vs) <*>.. xs)                             --. L (Def  "liftM")
    === ((us >>= \u -> vs >>= return . (u .)) <*>.. xs)                      --. L (Def  "<*>..")
    === ((us >>= \u -> vs >>= return . (u .)) >>= \f -> liftM f xs)          --. L (Prop "m3")
    === (us >>= \u -> vs >>= return . (u .) >>= \f -> liftM f xs)            --. L (Prop "m3") 
    === (us >>= \u -> vs >>= \v -> (return . (u .)) v >>= \f -> liftM f xs)  --. L (Def  ".")
    === (us >>= \u -> vs >>= \v -> return  (u . v) >>= \f -> liftM f xs)     --. L (Prop "m1")
    === (us >>= \u -> vs >>= \v ->  (\f -> liftM f xs) (u . v))              --. L Beta
    === (us >>= \u -> vs >>= \v ->  liftM (u . v) xs)                        --. QED

lemma2_tha4 :: Monad m => m (b -> c) -> m (a -> b) -> m a -> m c
lemma2_tha4 us vs xs = -- right hand side transformation
        (us <*>.. (vs <*>.. xs))                                   --. L (Def  "<*>..")
    === (us >>= \u -> liftM u (vs <*>.. xs))                       --. L (Def  "<*>..")
    === (us >>= \u -> liftM u (vs >>= \v -> liftM v xs))           --. L (Def  "liftM")
    === ((us >>= \u -> (vs >>= \v -> liftM v xs) >>= return . u))  --. L (Prop "m3")
    === ((us >>= \u -> vs >>= \v -> liftM v xs >>= return . u))    --. R (Def  "liftM")
    === (us >>= \u -> vs >>= \v -> liftM u (liftM v xs))           --. L (Prop "theoremFunctor2")
    === (us >>= \u -> vs >>= \v -> liftM (u . v) xs)               --. QED


--------------------------------------------
-- Законы класса Monad

{-
Покажите, что из законов класса типов Monad 

return a >>= k   ==  k a                     -- m1
m >>= return     ==  m                       -- m2
(m >>= v) >>= w  ==  m >>= (\x -> v x >>= w) -- m3

следует, что стрелки Клейсли образуют моноид относительно операции их композиции (>=>)
c return в качестве нейтрального элемента. Иными словами докажите, что верны равенства

return >=> k     ==  k
k >=> return     ==  k
(u >=> v) >=> w  ==  u >=> (v >=> w)
-}

-- Определение рыбки через >>=
(>=>) :: Monad m => (a -> m b) -> (b -> m c) -> a -> m c
g >=> h = \x -> g x >>= h

-- forall k. return >=> k  ==  k
fishLeftNeutral :: Monad m => (a -> m b) -> a -> m b
fishLeftNeutral k =
      (return >=> k)          --. L (Def  ">=>")
 === (\a -> return a >>= k)   --. L (Prop "m1")
 === (\a -> k a)              --. L Eta
 === k                        --. QED

-- forall k. k >=> return  ==  k
fishRightNeutral :: Monad m => (a -> m b) -> a -> m b
fishRightNeutral k =
     (k >=> return)           --. L (Def  ">=>")
 === (\a -> k a >>= return)   --. L (Prop "m2")
 === (\a -> k a)              --. L Eta
 === k                        --. QED

-- forall u v w. (u >=> v) >=> w  ==  u >=> (v >=> w)
fishAssoc :: Monad m => (a -> m b) -> (b -> m c) -> (c -> m d) -> a -> m d
fishAssoc u v w =
     ((u >=> v) >=> w)                    --. L (Def  ">=>")
 === (\a -> (u >=> v) a >>= w)            --. L (Def  ">=>")
 === (\a -> (\a' -> u a' >>= v) a >>= w)  --. L Beta
 === (\a -> (u a >>= v) >>= w)            --. L (Prop "m3")
 === (\a -> u a >>= \b -> v b >>= w)      --. R (Def  ">=>")
 === (\a -> u a >>= (v >=> w))            --. R (Def  ">=>")
 === (u >=> (v >=> w))                    --. QED

-----------------------------------------------------

{-
Покажите, что законы

join . return       ==  id           -- mjfr1
join . fmap return  ==  id           -- mjfr2
join . fmap join    ==  join . join  -- mjfr3

следуют из законов класса типов Monad

return a >>= k   ==  k a                     --. L (Prop "m1")
m >>= return     ==  m                       --. L (Prop "m2")
(m >>= v) >>= w  ==  m >>= (\x -> v x >>= w) --. L (Prop "m3")

используя реализации join через (>>=) и liftM через (>>=) и return.
-- 
join x  =  x >>= id 
liftM f xs  =  xs >>= return . f 
-}

join :: Monad m => m (m a) -> m a
join x  =  x >>= id 


--- (TODO если потом этим пользоваться как теоремой, то нужно научиться как-то экстрагировать отсюда эта-редуцированную версию)
--  join . return === id  -- :: m a -> m a
mjfr1 :: Monad m => m a -> m a
mjfr1 xs = 
     (join . return) xs   --. L (Def  ".")
 === join (return xs)     --. L (Def  "join")
 === (return xs >>= id)   --. L (Prop "m1")
 === id xs                --. QED

---
--   join . fmap return === id  -- :: m a -> m a
mjfr2 :: Monad m => m a -> m a
mjfr2 xs = 
     ((join . liftM return) xs)                --. L (Def  ".")
 === (join (liftM return xs))                  --. L (Def  "join")
 === (liftM return xs >>= id)                  --. L (Def  "liftM")
 === (xs >>= return . return >>= id)           --. L (Prop "m3")
 === (xs >>= \x -> (return . return) x >>= id) --. L (Def  ".")
 === (xs >>= \x -> return (return x) >>= id)   --. L (Prop "m1")
 === (xs >>= \x -> id (return x))              --. L (Def  "id")
 === (xs >>= \x -> return x)                   --. L Eta
 === (xs >>= return)                           --. L (Prop "m2")
 === xs                                        --. R (Def  "id")
 === id xs                                     --. QED

---
--  join . fmap join  ===  join . join  -- :: m (m (m a)) -> m a
mjfr3 :: Monad m => m (m (m a)) -> m a
mjfr3 x3s = 
     ((join . liftM join) x3s)                      --. L (Def  ".")
 === (join (liftM join x3s))                        --. L (Def  "liftM")
 === (join (x3s >>= return . join))                 --. L (Def  "join")
 === (x3s >>= return . join >>= id)                 --. L (Prop "m3")
 === ((x3s >>= \x2s -> (return . join) x2s >>= id)) --. L (Def  ".")
 === (x3s >>= \x2s -> return (join x2s) >>= id)     --. L (Prop "m1")
 === (x3s >>= \x2s -> id (join x2s))                --. L (Def  "id")
 === (x3s >>= \x2s -> join x2s)                     --. L (Def  "join")
 === (x3s >>= \x2s -> x2s >>= id)                   --. R (Def  "id")
 === (x3s >>= \x2s -> id x2s >>= id)                --. R (Prop "m3")
 === (x3s >>= id >>= id)                            --. R (Def  "join")
 === (join x3s >>= id)                              --. R (Def  "join")
 === (join (join x3s))                              --. R (Def  ".")
 === ((join . join) x3s)                            --. QED





----------------------------------------------------
----------------------------------------------------
-- Concrete Monad Laws
{-
return a >>= k  ===  k a                     -- 1 Monad Law
m >>= return    ===  m                       -- 2 Monad Law
m >>= k >>= k'  ===  m >>= \x -> k x >>= k'  -- 3 Monad Law
-}

-- Maybe (TODO для пруфчекинга типы и их инстансы надо выписывать явно или иметь встроенный псевдобиблиотечный референс)
-- {-
instance  Monad Maybe  where
  Just x  >>= k  =  k x     -- (1)
  Nothing >>= _  =  Nothing -- (2)

  return  =  Just
-- -}


-- forall a k . return a >>= k === k a
monad1LawMaybe :: a -> (a -> Maybe b) -> Maybe b
monad1LawMaybe a k =
     (return a >>= k)  --. L (Inst "return")
 === (Just a >>= k)    --. L (Inst ">>=")
 === k a               --. QED

-- forall m . m >>= return === m  
monad2LawMaybe ::  Maybe a -> Maybe a
monad2LawMaybe (Just a) =
     (Just a >>= return)   --. L (Inst ">>=")
 === return a              --. L (Inst "return")
 === Just a                --. QED
monad2LawMaybe Nothing =
     (Nothing >>= return)  --. L (Inst ">>=")
 === Nothing               --. QED

-- forall m k k' . m >>= k >>= k'  ===  m >>= \x -> k x >>= k'
monad3LawMaybe ::  Maybe a -> (a -> Maybe b) -> (b -> Maybe c) -> Maybe c
monad3LawMaybe (Just a) k k' =
     (Just a >>= \x -> k x >>= k')  --. L (Inst ">>=")
 === ((\x -> k x >>= k') a)         --. L Beta
 === (k a >>= k')                   --. R (Inst ">>=")
 === ((Just a >>= k) >>= k')        --. QED
monad3LawMaybe Nothing k k' =
     (Nothing >>= \x -> k x >>= k') --. L (Inst ">>=")
 === Nothing                        --. R (Inst ">>=")
 === (Nothing >>= k')               --. R (Inst ">>=")
 === ((Nothing >>= k) >>= k')       --. QED     



------ Monad Alternative in file ProofsMonad2


