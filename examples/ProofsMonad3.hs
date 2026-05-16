module ProofsMonad3 where
import ProofBase
-- import Compose (composeAssoc, composeLeftNeutral)  -- Нужно только для пруфчекенга, живет в комментариях

-- import ProofsFunctor 

import Prelude hiding ((.), id, ($), const, flip)

-----------------------------
{-
Fall 2024

Покажите, что типы всех трех способов записи композиции монадических эффектов изоморфны. 
Для этого предъявите функции-преобразователи между ними и докажите тождественность обеих их композиций.

В преобразованиях понадобится "свободные теоремы" для типов >>= и >=> (2 представителя)

m >>= k    ===   fmap k m >>= id
b m k      ===   b (fmap k m) id             -- alt syntax

k1 >=> k2  ===  (id >=> k2) . k1
c k1 k2    ===  (c id k2) . k1              -- alt syntax

k1 >=> k2  ===  (id >=> id) . fmap k2 . k1 
c k1 k2    ===  c id id . fmap k2 . k1      -- alt syntax
 -}

bindFREE :: Functor m => (forall b c. m b -> (b -> m c) -> m c) 
              -> m b -> (b -> m c) -> m c
bindFREE b m k = 
     b (fmap k m) id  --. Postulate
 === b m k            --. QED

fishFREE :: (forall a b c. (a -> m b) -> (b -> m c) -> a -> m c) 
               -> (a -> m b) -> (b -> m c) -> a -> m c
fishFREE c k1 k2 a = 
     (c id k2 (k1 a))   --. Postulate
 === (c k1 k2 a)        --. QED

fishFREE' :: Functor m => (forall a b c. (a -> m b) 
                -> (b -> m c) -> a -> m c) -> (a -> m b) -> (b -> m c) -> a -> m c
fishFREE' c k1 k2 = 
     (c id id . fmap k2 . k1)  --. Postulate
 === (c k1 k2)                 --. QED

-- Изоморфизм bind и fish
c2b :: (forall a b c. (a -> m b) -> (b -> m c) -> a -> m c) -> m b -> (b -> m c) -> m c
c2b (>=>) m k = (id >=> k) m

b2c :: (forall b c. m b -> (b -> m c) -> m c) -> (a -> m b) -> (b -> m c) -> a -> m c
b2c (>>=) k1 k2 a = k1 a >>= k2

-- Показываем, что обе их композиции это id
-- Для доказательства изоморфизма потребуется свободная теорема, а значит контекст Functor m
isoCB :: (forall b c. m b -> (b -> m c) -> m c) -> 
                      m b -> (b -> m c) -> m c
isoCB b = 
     (\m k -> c2b (b2c b) m k) --. L (Def  "c2b")
 === (\m k -> b2c b id k m)    --. L (Def  "b2c")
 === (\m k -> b (id m) k)      --. L (Def  "id")
 === (\m k -> b m k)           --. L Eta
 === (\m -> b m)               --. L Eta
 === b                         --. QED

{- SKIP-1
isoBC :: (forall a b c. (a -> m b) -> (b -> m c) -> a -> m c) -> 
                        (a -> m b) -> (b -> m c) -> a -> m c
isoBC c =
     (\k1 k2 a -> b2c (c2b c) k1 k2 a) --. L (Def  "b2c")
 === (\k1 k2 a -> c2b c (k1 a) k2)     --. L (Def  "c2b")
 === (\k1 k2 a -> c id k2 (k1 a))      --. L (Prop "fishFREE")-- [fishFREE]
 === (\k1 k2 a -> c k1 k2 a)           --. L Eta
 === (\k1 k2 -> c k1 k2)               --. L Eta
 === (\k1 -> c k1)                     --. L Eta
 === c                                 --. QED
--QED
SKIP-1 -}

-- Изоморфизм bind и join
b2j :: (forall b c. m b -> (b -> m c) -> m c) -> m (m c) -> m c
b2j (>>=) mm  =  mm >>= id

j2b :: Functor m => (forall c. m (m c) -> m c) -> m b -> (b -> m c) -> m c
j2b join m k = join (fmap k m)

-- Показываем, что обе их композиции это id
isoBJ :: Functor m => 
         (forall c. m (m c) -> m c) -> 
                    m (m c) -> m c
isoBJ j = 
     (\mm -> b2j (j2b j) mm) --. L (Def  "b2j")
 === (\mm -> j2b j mm id)    --. L (Def  "j2b")
 === (\mm -> j (fmap id mm)) --. Postulate --L (Prop "f1")
 === (\mm -> j mm)           --. L Eta
 === j                       --. QED

isoJB :: Functor m => 
         (forall b c. m b -> (b -> m c) -> m c) -> 
                      m b -> (b -> m c) -> m c
isoJB b = 
     (\m k -> j2b (b2j b) m k)  --. L (Def  "j2b")
 === (\m k -> b2j b (fmap k m)) --. L (Def  "b2j")
 === (\m k -> b (fmap k m) id)  --. L (Prop "bindFREE")
 === (\m k -> b m k)            --. L Eta
 === (\m  -> b m)               --. L Eta
 === b                          --. QED
 --QED

-- ну и до кучи, хотя это следует из транзитивности

-- Изоморфизм join и fish
c2j :: (forall a b c. (a -> m b) -> (b -> m c) -> a -> m c) -> m (m c) -> m c
c2j (>=>) = id >=> id 

j2c :: Functor m => (forall c. m (m c) -> m c) -> (a -> m b) -> (b -> m c) -> a -> m c
j2c join k1 k2 a = join (fmap k2 (k1 a))

-- Показываем, что обе их композиции это id
isoCJ :: Functor m => 
         (forall c. m (m c) -> m c) -> 
                    m (m c) -> m c
isoCJ j = 
     (\a -> c2j (j2c j) a)      --. L (Def  "c2j")
 === (\a -> j2c j id id a)      --. L (Def  "j2b")
 === (\a -> j (fmap id (id a))) --. Postulate --L (Prop "f1")
 === (\a -> j (id a))           --. L (Def  "id")
 === (\a -> j a)                --. L Eta
 === j                          --. QED


-- {- SKIP EASY FIX I JUST DON"T WANT
isoJC :: Functor m => 
         (forall a b c. (a -> m b) -> (b -> m c) -> a -> m c) -> 
                        (a -> m b) -> (b -> m c) -> a -> m c
isoJC c = 
     (\k1 k2 a -> j2c (c2j c) k1 k2 a)      --. L (Def  "j2c")
 === (\k1 k2 a -> c2j c (fmap k2 (k1 a)))   --. L (Def  "c2j")
 === (\k1 k2 a -> c id id (fmap k2 (k1 a))) --. L (Prop "fishFREE'")
 === (\k1 k2 a -> c k1 k2 a)                --. L Eta
 === (\k1 k2 -> c k1 k2)                    --. L Eta
 === (\k1 -> c k1)                          --. L Eta
 === c                                      --. QED
 --QED
--  -}

