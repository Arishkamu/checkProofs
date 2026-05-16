module ProofsMonad where

import Prelude hiding ((.), ($), id, flip)
import ProofBase
-- доказательства в виде равенств, не проверяемых системой содержательно, но контролируемых по типу 
-- псевдоэквивалентность, обеспечивает только правильность типизации
-- import ProofsBase ( (===) )
-- infixl 0 ===
-- (===) :: a -> a -> a
-- (===) = const

{-
СИНТАКСИС КОММЕНТАРИЕВ
eta-reduction     -- применена или контрпременена бета-редукция
L Beta-reduction    -- применена или контрпременена эта-редукция

liftM             -- применено или контрпременено определение функции (NB должно быть доступно)
foldr (2)         -- применено или контрпременено определение функции (с уточнением конкретного равенства в определении) 

[theoremFunctor1] -- применена или контрпременена теорема

{POSTULATE}       -- не пруфчекаем переход, верим на слово

inst return       -- применено или контрпременено определение реализации метода представителя для класса типов 
                  -- (TODO надо ли указывать для какого типа? Или это всегда выводится?)


-}





--- ANOTHER FILE
composeAssoc4 :: (c -> d) -> (b -> c) -> (a -> b) -> a -> d
composeAssoc4 f g h =
    (f . (g . h))                    --. L (Def  ".")
 === (\x -> f ((g . h) x))           --. L (Def  ".")
 === (\x -> f ((\x' -> g (h x')) x)) --. L Beta
 === (\x -> f (g (h x)))             --. L Beta
 === (\x -> (\x' -> f (g x')) (h x)) --. R (Def  ".")
 === (\x -> (f . g) (h x))           --. R (Def  ".")
 === ((f . g) . h)                   --. QED


composeLeftNeutral :: (a -> b) -> a -> b
composeLeftNeutral f =
      (id . f)           --. L (Def  ".")
 === (\x -> id (f x))    --. L (Def  "id")
 === (\x -> f x)         --. L Eta
 === f                   --. QED

composeRightNeutral :: (a -> b) -> a -> b
composeRightNeutral f =
      (f . id)        --. L (Def  ".")
 === (\x -> f (id x)) --. L (Def  "id")
 === (\x -> f x)      --. L Eta
 === f                --. QED


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
flipFlipIsId' f x y =
      flip (flip f) x y  --. L (Def  "flip")
 === flip f y x          --. L (Def  "flip")
 === f x y               --. QED




{- TODO надо продумать как давать канонические определения типа (.) и ($) и часто используемые теоремы типа ассоциативности композиции  -}

------------------------------------------------------------------
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
 === (k a)            --. QED

m2 :: Monad m => m a -> m a
m2 m =
     (m >>= return) --. Postulate
 === m              --. QED

m3 :: Monad m => m a -> (a -> m b) -> (b -> m c) -> m c
m3 m k k' =
     (m >>= k >>= k')          --. Postulate
 ===  (m >>= \x -> k x >>= k') --. QED

{-
Покажите, что каждая монада - это функтор. 
Для этого выразите fmap через (>>=) и return:
-}
liftM :: Monad m => (a -> b) -> m a -> m b
liftM f xs  =  xs >>= return . f
--liftM f xs  =  xs >>= \x -> return (f x)
-- Control.Monad.liftM
{-
Для полноценного доказательства следует еще проверить выполнение законов класса Functor.
-}
{-
1 Functor law
liftM id xs == xs
-}
theoremFunctor1 :: Monad m => m b -> m b
theoremFunctor1 xs =
  (liftM id xs)                      --. L (Def  "liftM")
  === (xs >>= return . id)           --. L (Def  ".")
  === (xs >>= \x -> return (id x))   --. L (Def  "id")
  === (xs >>= \x -> return x)        --. L Eta
  === (xs >>= return)                --. L (Prop "m2")
  === xs                             --. QED
{-
2 Functor law
liftM (f . g) xs == liftM f (liftM g xs)
-}
theoremFunctor2 :: Monad m => (b -> c) -> (a -> b) -> m a -> m c
theoremFunctor2 f g xs =
       (liftM f (liftM g xs))                      --. L (Def  "liftM")-- liftM
  === (liftM f (xs >>= return . g))                --. L (Def  "liftM")-- liftM
  === ((xs >>= return . g) >>= return . f)         --. L (Prop "m3")-- [m3]
  === (xs >>= \x -> (return . g) x >>= return . f) --. L (Def  ".")-- (.)
  === (xs >>= \x -> return (g x) >>= return . f)   --. L (Prop "m1")-- [m1]
  === (xs >>= \x -> (return . f) (g x))            --. R (Def  ".")-- (.)
  === (xs >>= \x -> ((return . f) . g) x)          --. L Eta-- eta-reduction
  === (xs >>= (return . f) . g)                    --. R (Prop "composeAssoc4")-- assoc (.) ?????????
  === (xs >>= return . (f . g))                    --. R (Def  "liftM")-- liftM
  === (liftM (f . g) xs)                           --. QED

-- f . (g . h) === (f . g) . h

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
liftM g xs == return g <*>.. xs
-}
theoremApplicative0 :: Monad m => (a -> b) -> m a -> m b
theoremApplicative0 g xs =
       (return g <*>.. xs)             --. L (Def  "<*>..")-- (<*>..)
  === (return g >>= \f -> liftM f xs)  --. L (Prop "m1")-- [m1]
  === ((\f -> liftM f xs) g)           --. L Beta-- L Beta-reduction
  === (liftM g xs)                     --. QED

{-
1 Applicative law (Identity)
return id <*>.. xs  == xs
-}
theoremApplicative1 :: Monad m => m b -> m b
theoremApplicative1 xs =
       (return id <*>.. xs)              --. L (Def  "<*>..")-- (<*>..)
  === (return id >>= \f -> liftM f xs)   --. L (Prop "m1")-- [m1]
  === ((\f -> liftM f xs) id)            --. L Beta-- L Beta-reduction
  === (liftM id xs)                      --. L (Prop "theoremFunctor1")-- [theoremFunctor1]
  === xs                                 --. QED

{-
2 Applicative law (Homomorphism)
return g <*>.. return x  == return (g x)
-}
theoremApplicative2 :: Monad m => (a -> b) ->  a -> m b
theoremApplicative2 g x =
       (return g <*>.. return x)              --. L (Def  "<*>..")-- (<*>..)
  === (return g >>= \f -> liftM f (return x)) --. L (Prop "m1")-- [m1]
  === ((\f -> liftM f (return x)) g)          --. L Beta-- L Beta-reduction
  === (liftM g (return x))                    --. L (Def  "liftM")-- liftM
  === (return x >>= return . g)               --. L (Prop "m1")-- [m1]
  === ((return . g) x )                       --. L (Def  ".")-- (.)
  === (return (g x))                          --. QED

{-
3 Applicative law (Interchange)
fs <*>.. return x  ===  return ($ x) <*>.. fs
-}
theoremApplicative3 :: Monad m => m (a -> b) -> a -> m b
theoremApplicative3 fs x =
       (fs <*>.. return x )        --. L  (Prop "lemma1")-- [lemma1]
  === (fs >>= \f -> return (f x))  --. R (Prop "lemma2")-- [lemma2]
  === (return ($ x) <*>.. fs)      --. QED


lemma1 fs x = -- L hand side transformation
        (fs <*>.. return x )                    --. L (Def  "<*>..")-- (<*>..)
    === (fs >>= \f -> liftM f (return x))       --. L (Def  "liftM") -- liftM
    === (fs >>= \f -> return x >>= return . f)  --. L (Prop "m1")-- [m1]
    === (fs >>= \f -> (return . f) x )          --. L (Def  ".")-- (.)
    === (fs >>= \f -> return (f x))             --. QED

lemma2 fs x = -- R hand side transformation
        (return ($ x) <*>.. fs)              --. L (Def  "<*>..")-- (<*>..)
    === (return ($ x) >>= \f -> liftM f fs)  --. L (Prop "m1")-- [m1]
    === ((\f -> liftM f fs) ($ x))           --. L Beta-- L Beta-reduction
    === (liftM ($ x) fs )                    --. L (Def  "liftM")-- liftM
    === (fs >>= return . ($ x))              --. L (Def  ".")-- (.)
    === (fs >>= \f -> return (($ x) f))      --. L (Def  "$")-- ($)
    === (fs >>= \f -> return (f x))          --. QED

-- Expected: App :: >>=
--   @m_a1mZ
--   $dMonad_a1n2
--   @(a_a1n0 -> b_a1n1)
--   @b_a1n1
--   fs_aBU
--   (\ (f_aBW :: a_a1n0 -> b_a1n1) ->
--      return @m_a1mZ $dMonad_a1n2 @b_a1n1 (f_aBW x_aBV))
-- Got: App :: <*>..
-- @m_a1mZ
-- @a_a1n0
-- @b_a1n1
-- $dMonad_a1n2
-- fs_aBU
-- (return @m_a1mZ $dMonad_a1n2 @a_a1n0 x_aBV)

{-
4 Applicative law (Composition)
return (.) <*>.. us <*>.. vs <*>.. xs  ==  us <*>.. (vs <*>.. xs)
-}
theoremApplicative4 :: Monad m => m (b -> c) -> m (a -> b) -> m a -> m c
theoremApplicative4 us vs xs =
      (return (.) <*>.. us <*>.. vs <*>.. xs )      --. L (Prop "ta4_lemma1")-- [lemma1]
 === (us >>= \u -> vs >>= \v -> liftM (u . v) xs)   --. R (Prop "ta4_lemma2")-- [lemma2]
 === (us <*>.. (vs <*>.. xs))                       --. QED

ta4_lemma1 :: Monad m => m (b -> c) -> m (a -> b) -> m a -> m c
ta4_lemma1 us vs xs = -- L hand side transformation
      (return (.) <*>.. us <*>.. vs <*>.. xs )                            --. L (Def  "<*>..")-- (<*>..)
 === ((return (.) >>= \c -> liftM c us) <*>.. vs <*>.. xs)                --. L (Prop "m1")-- [m1]
 === ((\c -> liftM c us) (.) <*>.. vs <*>.. xs)                           --. L Beta-- L Beta-reduction
 === (liftM (.) us <*>.. vs <*>.. xs)                                     --. L (Def  "liftM")-- liftM
 === ((us >>= return . (.)) <*>.. vs <*>.. xs)                            --. L (Def  "<*>..")-- (<*>..)
 === (((us >>= return . (.)) >>= \r -> liftM r vs) <*>.. xs)              --. L (Prop "m3")-- [m3] 
 === ((us >>= \u -> (return . (.)) u >>= \r -> liftM r vs) <*>.. xs)      --. L (Def  ".")-- (.)
 === ((us >>= \u -> return (u .) >>= \r -> liftM r vs) <*>.. xs)          --. L (Prop "m1")-- [m1]
 === ((us >>= \u -> (\r -> liftM r vs) (u .)) <*>.. xs)                   --. L Beta-- L Beta-reduction
 === ((us >>= \u -> liftM (u .) vs) <*>.. xs)                             --. L (Def  "liftM")-- liftM
 === ((us >>= \u -> vs >>= return . (u .)) <*>.. xs)                      --. L (Def  "<*>..")-- (<*>..)
 === ((us >>= \u -> vs >>= return . (u .)) >>= \f -> liftM f xs)          --. L (Prop "m3")
--  === ((us >>= \u -> vs >>= return . (u .)) >>= \f -> liftM f xs)         --. L Beta-- [m3] + L Beta-reduction ??????? TODO продумать многошаговость, если не вложенная, то, вроде, несложно
 === (us >>= \u -> vs >>= return . (u .) >>= \f -> liftM f xs)            --. L (Prop "m3")-- [m3] 
 === (us >>= \u -> vs >>= \v -> (return . (u .)) v >>= \f -> liftM f xs)  --. L (Def  ".")-- L Beta-reduction
 === (us >>= \u -> vs >>= \v -> return  (u . v) >>= \f -> liftM f xs)     --. L (Prop "m1")-- [m1]
 === (us >>= \u -> vs >>= \v ->  (\f -> liftM f xs) (u . v))              --. L Beta-- L Beta-reduction
 === (us >>= \u -> vs >>= \v ->  liftM (u . v) xs)                        --. QED

-- -- m3 m k k' = (m >>= k >>= k')  `postulate`  (m >>= \x -> k x >>= k')

ta4_lemma2 :: Monad m => m (b -> c) -> m (a -> b) -> m a -> m c
ta4_lemma2 us vs xs = -- R hand side transformation
      (us <*>.. (vs <*>.. xs) )                               --. L (Def  "<*>..")-- (<*>..)
 === (us >>= \u -> liftM u (vs <*>.. xs))                     --. L (Def  "<*>..")-- (<*>..)
 === (us >>= \u -> liftM u (vs >>= \v -> liftM v xs))         --. L (Def  "liftM") -- liftM
 === (us >>= \u -> (vs >>= \v -> liftM v xs) >>= return . u)  --. L (Prop "m3")-- [m3] + L Beta-reduction ??????
--  === (us >>= \x -> (\u -> (vs >>= \v -> liftM v xs)) x >>= return . u)  -- [m3] + L Beta-reduction ??????
 === (us >>= \u -> vs >>= \v -> liftM v xs >>= return . u)    --. R (Def  "liftM")-- liftM
 === (us >>= \u -> vs >>= \v -> liftM u (liftM v xs) )        --. L (Prop "theoremFunctor2") -- [theoremFunctor2]
 === (us >>= \u -> vs >>= \v -> liftM (u . v) xs)             --. QED

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

-- return >=> k  ==  k
fishLeftNeutral :: Monad m => (a -> m b) -> a -> m b
fishLeftNeutral k =
      (return >=> k)        --. L (Def  ">=>") -- >=>
 === (\a -> return a >>= k) --. L (Prop "m1")-- [m1]
 === (\a -> k a)            --. L Eta-- eta-reduction
 === k                      --. QED

-- k >=> return  ==  k
fishRightNeutral :: Monad m => (a -> m b) -> a -> m b
fishRightNeutral k =
      (k >=> return)        --. L (Def  ">=>")  -- >=>
 === (\a -> k a >>= return) --. L (Prop "m2")-- [m2]
 === (\a -> k a)            --. L Eta-- eta-reduction
 === k                      --. QED

-- (u >=> v) >=> w  ==  u >=> (v >=> w)
fishAssoc :: Monad m => (a -> m b) -> (b -> m c) -> (c -> m d) -> a -> m d
fishAssoc u v w =
      ((u >=> v) >=> w)                     --. L (Def  ">=>")-- >=>
 === (\a -> (u >=> v) a >>= w)              --. L (Def  ">=>")-- >=>
 === (\a -> (\a' -> u a' >>= v) a >>= w)    --. L Beta-- L Beta-reduction
 === (\a -> (u a >>= v) >>= w)              --. L (Prop "m3")-- [m3]
 === (\a -> u a >>= \b -> v b >>= w)        --. R (Def  ">=>")-- >=>
 === (\a -> u a >>= (v >=> w))              --. R (Def  ">=>")-- >=>
 === (u >=> (v >=> w))                      --. QED

-----------------------------------------------------

{-
Покажите, что законы

join . return       ==  id           -- mjfr1
join . fmap return  ==  id           -- mjfr2
join . fmap join    ==  join . join  -- mjfr3

следуют из законов класса типов Monad

return a >>= k   ==  k a                     -- [m1]
m >>= return     ==  m                       -- [m2]
(m >>= v) >>= w  ==  m >>= (\x -> v x >>= w) -- [m3]

используя реализации join через (>>=) и liftM через (>>=) и return.
-- 
join x  =  x >>= id 
liftM f xs  =  xs >>= return . f 
-}

join :: Monad m => m (m a) -> m a
join x  =  x >>= id 

--- (TODO если потом этим пользоваться как теоремой, то нужно научиться как-то экстрагировать отсюда эта-редуцированную версию)
--  join . return == id  -- :: m a -> m a
mjfr1 :: Monad m => m a -> m a
mjfr1 xs =
      ((join . return) xs)   --. L (Def  ".")-- (.)
 === (join (return xs))      --. L (Def  "join")-- join
 === ( return xs >>= id)     --. L (Prop "m1")-- [m1]
 === ( id xs)                --. L (Def  "id")-- id
 === ( xs)                   --. QED -- id

---
--   join . fmap return == id  -- :: m a -> m a
mjfr2 :: Monad m => m a -> m a
mjfr2 xs =
     ((join . liftM return) xs )                --. L (Def  ".")-- (.)
 === ( join (liftM return xs)  )                --. L (Def  "join")-- join
 === ( liftM return xs >>= id   )               --. L (Def  "liftM") -- liftM
 === ( xs >>= return . return >>= id  )         --. L (Prop "m3")-- [m3]
 === ( xs >>= \x -> (return . return) x >>= id) --. L (Def  ".")-- (.)
 === ( xs >>= \x -> return (return x) >>= id)   --. L (Prop "m1")-- [m1]
 === ( xs >>= \x -> id (return x))              --. L (Def  "id")-- id
 === ( xs >>= \x -> return x  )                 --. L Eta-- eta-reduction
 === ( xs >>= return)                           --. L (Prop "m2")-- [m2]
 === ( xs      )                                --. R (Def  "id")-- id
 === ( id xs)                                   --. QED -- id

---
--  join . fmap join  ==  join . join  -- :: m (m (m a)) -> m a
mjfr3 :: Monad m => m (m (m a)) -> m a
mjfr3 x3s =
     ((join . liftM join) x3s  )                   --. L (Def  ".")-- (.)
 === ( join (liftM join x3s)     )                 --. L (Def  "liftM")-- liftM
 === ( join (x3s >>= return . join) )              --. L (Def  "join")-- join
 === ( x3s >>= return . join >>= id )              --. L (Prop "m3")-- [m3]
 === ( x3s >>= \x2s -> (return . join) x2s >>= id) --. L (Def  ".")-- (.)
 === ( x3s >>= \x2s -> return (join x2s) >>= id)   --. L (Prop "m1")-- [m1]
 === ( x3s >>= \x2s -> id (join x2s))              --. L (Def  "id")-- id
 === ( x3s >>= \x2s -> join x2s     )              --. L (Def  "join")-- join
 === ( x3s >>= \x2s -> x2s >>= id )                --. R (Def  "id")-- id
 === ( x3s >>= \x2s -> id x2s >>= id )             --. R (Prop "m3")-- [m3]
 === ( x3s >>= id >>= id )                         --. R (Def  "join")  -- join
 === ( join x3s >>= id )                           --. R (Def  "join") -- join
 === ( join (join x3s)   )                         --. R (Def  ".") -- (.)
 === ( (join . join) x3s)                          --. QED -- id





----------------------------------------------------
----------------------------------------------------
-- Concrete Monad Laws
{-
return a >>= k  ===  k a                     -- 1 Monad Law
m >>= return    ===  m                       -- 2 Monad Law
m >>= k >>= k'  ===  m >>= \x -> k x >>= k'  -- 3 Monad Law
-}

-- Maybe (TODO для пруфчекинга типы и их инстансы надо выписывать явно или иметь встроенный псевдобиблиотечный референс)
{-
instance  Monad Maybe  where
  Just x  >>= k  =  k x     -- (1)
  Nothing >>= _  =  Nothing -- (2)

  return  =  Just
-}
-- monad1LawMaybe :: a -> (a -> Maybe b) -> Maybe b
-- monad1LawMaybe a k =
--      return a >>= k  -- inst return
--  === Just a >>= k    -- inst (>>=) (1)
--  === k a

-- monad2LawMaybe ::  Maybe a -> Maybe a
-- monad2LawMaybe (Just a) =
--      Just a >>= return   -- inst (>>=) (1)
--  === return a            -- inst return
--  === Just a
-- monad2LawMaybe Nothing =
--      Nothing >>= return  -- inst (>>=) (2)
--  === Nothing

-- monad3LawMaybe ::  Maybe a -> (a -> Maybe b) -> (b -> Maybe c) -> Maybe c
-- monad3LawMaybe (Just a) k k' =
--      Just a >>= \x -> k x >>= k'  -- inst (>>=) (1)
--  === (\x -> k x >>= k') a         -- L Beta-reduction
--  === k a >>= k'                   -- inst (>>=) (1)
--  === (Just a >>= k) >>= k'
-- monad3LawMaybe Nothing k k' =
--      Nothing >>= \x -> k x >>= k' -- inst (>>=) (2)
--  === Nothing                      -- inst (>>=) (2)
--  === Nothing >>= k'               -- inst (>>=) (2)
--  === (Nothing >>= k) >>= k'          


 -- Lists (TODO тут понадобятся гипотезы индукции, это второй этап)