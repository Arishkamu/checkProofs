module ProofsFunctor where
import ProofBase
-- import Compose (composeAssoc, composeLeftNeutral)  -- Нужно только для пруфчекенга, живет в комментариях
import Prelude hiding ((.), id, ($), const, flip, Functor(..), Applicative(..))
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
 
-- {- Maybe
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
-- Maybe -}

-- {- List
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
-- List -}


-- {- Either
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
-- Either -}


-- {- PAIRS
-- Pair
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
-- PAIRS -}

-- {- Arrow
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
 === (g . (h . f))         --. Postulate --L (Def  ".") assoc
 === ((g . h) . f)         --. R (Inst "fmap")
 === fmap (g . h) f        --. QED
-- Arrow -}

-- {- CMPS
-- Cmps
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
-- CMPS -}

-- {- STATE
-- State

newtype State s a = State (s -> (s, a)) --{ runState :: s -> (s, a) }
runState :: State s a -> s -> (s, a)
runState (State f) a = f a

instance Functor (State s) where
  fmap :: (a -> b) -> State s a -> State s b
  fmap f (State g) = State (\s -> case g s of (s', a) -> (s', f a)) -- let (s', a) = g s in (s', f a))

{- STATE f1L
--functor1LawState ::  (e -> a) -> (e -> a)
functor1LawState :: State s b -> State s b
functor1LawState (State g) =
     fmap id (State g)                               --. L (Inst "fmap")
 === State (\s -> case g s of (s', a) -> (s', id a)) --. L (Def  "id")
 === State (\s -> case g s of (s', a) -> (s', a))    --. Postulate -- UNCASE??
 === State (\s -> g s)                               --. L Eta
 === State g                                         --. QED
STATE f1L -}

functor2LawState :: (b -> c) -> (a -> b) -> (e -> a) -> (e -> c)
functor2LawState g h f =
     (fmap g . fmap h) f   --. L (Def  ".")
 === fmap g (fmap h f)     --. L (Inst "fmap")
 === fmap g (h . f)        --. L (Inst "fmap")
 === (g . (h . f))         --. Postulate -- L (Def  ".")
 === ((g . h) . f)         --. R (Inst "fmap")
 === fmap (g . h) f        --. QED

-- STATE -}

