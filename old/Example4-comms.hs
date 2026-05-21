module ProofsMonad where
-- доказательства в виде равенств, не проверяемых системой содержательно, но контролируемых по типу 
-- псевдоэквивалентность, обеспечивает только правильность типизации
-- import ProofsBase ( (===) )
-- infixl 0 ===
-- (===) :: a -> a -> a
-- (===) = const

{-
СИНТАКСИС КОММЕНТАРИЕВ
eta-reduction     -- применена или контрпременена бета-редукция
beta-reduction    -- применена или контрпременена эта-редукция

liftM             -- применено или контрпременено определение функции (NB должно быть доступно)
foldr (2)         -- применено или контрпременено определение функции (с уточнением конкретного равенства в определении) 

[theoremFunctor1] -- применена или контрпременена теорема

{POSTULATE}       -- не пруфчекаем переход, верим на слово

inst return       -- применено или контрпременено определение реализации метода представителя для класса типов 
                  -- (TODO надо ли указывать для какого типа? Или это всегда выводится?)


-}


type SideExprInfo = Either ExprInfo ExprInfo

lFunc str = Left (Func str)
rFunc str = Right (Func str)
lPostl str = Left (Postl str)
rPostl str = Right (Postl str)
lEta = lEta
rEta = Right Eta
beta = Left Beta

data ExprInfo = Func String | Postl String | Beta | Eta
data WithInfo a = WithInfo { value :: a, info :: SideExprInfo}

addInfo :: a -> SideExprInfo -> WithInfo a
addInfo x info = WithInfo x info

postulate :: a -> a -> a
postulate = const

infixl 0 ====
(====) :: WithInfo a -> WithInfo a -> WithInfo a
(====) x y = y


-- MY FUNCTIONS
infixr 9 =.
(=.)    :: (b -> c) -> (a -> b) -> a -> c
(=.) f g = \x -> f (g x)

infixr 0 =$
(=$)    :: (a -> b) -> a -> b
(=$) f x = f x

myId                      :: a -> a
myId x                    =  x

myFlip :: (a -> b -> c) -> b -> a -> c
myFlip f x y              =  f y x









--- ANOTHER FILE
composeAssoc4 :: (c -> d) -> (b -> c) -> (a -> b) -> a -> d
composeAssoc4 f g h = value (
    (f =. (g =. h))                   `addInfo` lFunc "=."
 ==== (\x -> f ((g =. h) x))          `addInfo` lFunc "=."
 ==== (\x -> f ((\x' -> g (h x')) x)) `addInfo` beta
 ==== (\x -> f (g (h x)))             `addInfo` beta
 ==== (\x -> (\x' -> f (g x')) (h x)) `addInfo` lFunc "=."
 ==== (\x -> (f =. g) (h x))          `addInfo` lFunc "=."
 ==== ((f =. g) =. h)                 `addInfo` lFunc "=.")


composeLeftNeutral :: (a -> b) -> a -> b
composeLeftNeutral f = value (
      (myId =. f)           `addInfo` lFunc "=."
 ==== (\x -> myId (f x))    `addInfo` lFunc "myId"
 ==== (\x -> f x)           `addInfo` lEta
 ==== f                     `addInfo` lFunc "=.")

composeRightNeutral :: (a -> b) -> a -> b
composeRightNeutral f = value (
      (f =. myId)        `addInfo` lFunc "=."
 ==== (\x -> f (myId x)) `addInfo` lFunc "myId"
 ==== (\x -> f x)        `addInfo` lEta
 ==== f                  `addInfo` beta)


flipFlipIsId :: (a -> b -> c) -> a -> b -> c
flipFlipIsId  = value (
     (myFlip =. myFlip)                         `addInfo` lFunc "=."
 ==== (\f -> myFlip (myFlip f))                 `addInfo` rEta
 ==== (\f -> \x -> myFlip (myFlip f) x)         `addInfo` rEta
 ==== (\f -> \x -> \y -> myFlip (myFlip f) x y) `addInfo` lFunc "myFlip"
 ==== (\f -> \x -> \y -> myFlip f y x)          `addInfo` lFunc "myFlip"
 ==== (\f -> \x -> \y -> f x y)                 `addInfo` lEta
 ==== (\f -> \x -> f x)                         `addInfo` lEta
 ==== (\f -> f)                                 `addInfo` lFunc "myId"
 ==== (\f -> myId f)                            `addInfo` lEta
 ==== myId                                      `addInfo` lEta)

{- forall f x y. myFlip (myFlip f) x y ==== f x y -}
flipFlipIsId' :: (a -> b -> c) -> a -> b -> c
flipFlipIsId' f x y = value (
      myFlip (myFlip f) x y  `addInfo` lFunc "myFlip"
 ==== myFlip f y x           `addInfo` lFunc "myFlip"
 ==== f x y                  `addInfo` lEta)






{- TODO надо продумать как давать канонические определения типа (.) и ($) и часто используемые теоремы типа ассоциативности композиции  -}

------------------------------------------------------------------
-- MonadLaws
{-
return a >>= k  ===  k a                     -- 1 Monad Law
m >>= return    ===  m                       -- 2 Monad Law
m >>= k >>= k'  ===  m >>= \x -> k x >>= k'  -- 3 Monad Law
-}
-- postulates (это не доказывается, а является частью определения монады)
myM1 :: Monad m => a -> (a -> m b) -> m b
myM1 a k =
     (return a >>= k) -- {POSTULATE}
 `postulate` (k a)

myM2 :: Monad m => m a -> m a
myM2 m =
     (m >>= return)    -- {POSTULATE}
 `postulate` m

myM3 :: Monad m => m a -> (a -> m b) -> (b -> m c) -> m c
myM3 m k k' =
     (m >>= k >>= k')   -- {POSTULATE}
 `postulate`  (m >>= \x -> k x >>= k')

{-
Покажите, что каждая монада - это функтор. 
Для этого выразите fmap через (>>=) и return:
-}
myLiftM :: Monad m => (a -> b) -> m a -> m b
myLiftM f xs  =  xs >>= return =. f
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
theoremFunctor1 xs = value (
  (myLiftM myId xs)                      `addInfo` lFunc "myLiftM"
  ==== (xs >>= return =. myId)           `addInfo` lFunc "=."
  ==== (xs >>= \x -> return (myId x))  `addInfo` lFunc "myId"
  ==== (xs >>= \x -> return x)         `addInfo` lEta
  ==== (xs >>= return)                 `addInfo` lPostl "myM2"
  ==== xs                              `addInfo` beta)
{-
2 Functor law
liftM (f . g) xs == liftM f (liftM g xs)
-}
theoremFunctor2 :: Monad m => (b -> c) -> (a -> b) -> m a -> m c
theoremFunctor2 f g xs = value (
       (myLiftM f (myLiftM g xs))                     `addInfo` lFunc "myLiftM"-- liftM
  ==== (myLiftM f (xs >>= return =. g))               `addInfo` lFunc "myLiftM"-- liftM
  ==== ((xs >>= return =. g) >>= return =. f)         `addInfo` lPostl "myM3"-- [m3]
  ==== (xs >>= \x -> (return =. g) x >>= return =. f) `addInfo` lFunc "=."-- (.)
  ==== (xs >>= \x -> return (g x) >>= return =. f)    `addInfo` lPostl "myM1"-- [m1]
  ==== (xs >>= \x -> (return =. f) (g x))             `addInfo` rFunc "=."-- (.)
  ==== (xs >>= \x -> ((return =. f) =. g) x)          `addInfo` lEta-- eta-reduction
  ==== (xs >>= (return =. f) =. g)                    `addInfo` rFunc "composeAssoc4"-- assoc (.) ?????????
  ==== (xs >>= return =. (f =. g))                    `addInfo` rFunc "myLiftM"-- liftM
  ==== (myLiftM (f =. g) xs)                          `addInfo` beta)

-----------------------------------------------------------------------------------
{-
Покажите, что каждая монада --- это аппликативный функтор. 
Для этого выразите (<*>) :: Applicative f => f (a -> b) -> f a -> f b
на языке монад:
-}
(<*>..) :: Monad m => m (a -> b) -> m a -> m b
fs <*>.. xs = fs >>= \f -> myLiftM f xs -- см. liftM выше
{-
Для полноценного доказательства следует еще проверить выполнение законов класса Applicative.
-}
{-
0 Applicative law
liftM g xs == return g <*>.. xs
-}
theoremApplicative0 :: Monad m => (a -> b) -> m a -> m b
theoremApplicative0 g xs = value (
       (return g <*>.. xs)                `addInfo` rFunc "<*>.."-- (<*>..)
  ==== (return g >>= \f -> myLiftM f xs)  `addInfo` lPostl "myM1"-- [m1]
  ==== ((\f -> myLiftM f xs) g)           `addInfo` beta-- beta-reduction
  ==== (myLiftM g xs)                     `addInfo` beta)

{-
1 Applicative law (Identity)
return id <*>.. xs  == xs
-}
theoremApplicative1 :: Monad m => m b -> m b
theoremApplicative1 xs = value (
       (return myId <*>.. xs)                 `addInfo` lFunc "<*>.."-- (<*>..)
  ==== (return myId >>= \f -> myLiftM f xs)   `addInfo` lPostl "myM1"-- [m1]
  ==== ((\f -> myLiftM f xs) myId)            `addInfo` beta-- beta-reduction
  ==== (myLiftM myId xs)                      `addInfo` lPostl "theoremFunctor1"-- [theoremFunctor1]
  ==== xs                                     `addInfo` beta)

{-
2 Applicative law (Homomorphism)
return g <*>.. return x  == return (g x)
-}
theoremApplicative2 :: Monad m => (a -> b) ->  a -> m b
theoremApplicative2 g x = value (
       (return g <*>.. return x)                 `addInfo` lFunc "<*>.."-- (<*>..)
  ==== (return g >>= \f -> myLiftM f (return x)) `addInfo` lPostl "myM1"-- [m1]
  ==== ((\f -> myLiftM f (return x)) g)          `addInfo` beta-- beta-reduction
  ==== (myLiftM g (return x))                    `addInfo` lFunc "myLiftM"-- myLiftM
  ==== (return x >>= return =. g)                `addInfo` lPostl "myM1"-- [m1]
  ==== ((return =. g) x )                        `addInfo` lFunc "=."-- (=.)
  ==== (return (g x))                             `addInfo` beta)

{-
3 Applicative law (Interchange)
fs <*>.. return x  ===  return ($ x) <*>.. fs
-}
theoremApplicative3 :: Monad m => m (a -> b) -> a -> m b
theoremApplicative3 fs x = value (
       (fs <*>.. return x )         `addInfo` lPostl "lemma1"-- [lemma1]
  ==== (fs >>= \f -> return (f x))  `addInfo` lPostl "lemma2"-- [lemma2]
  ==== (return ($ x) <*>.. fs)      `addInfo` beta)
  where
    lemma1 = value (-- left hand side transformation
           (fs <*>.. return x )                    `addInfo` lFunc "<*>.."-- (<*>..)
      ==== (fs >>= \f -> myLiftM f (return x))      `addInfo` lFunc "myLiftM" -- myLiftM
      ==== (fs >>= \f -> return x >>= return =. f)  `addInfo` lPostl "myM1"-- [m1]
      ==== (fs >>= \f -> (return =. f) x )          `addInfo` lFunc "=."-- (=.)
      ==== (fs >>= \f -> return (f x))              `addInfo` beta)
    lemma2 = value (-- right hand side transformation
           (return ($ x) <*>.. fs)                `addInfo` lFunc "<*>.."-- (<*>..)
      ==== (return ($ x) >>= \f -> myLiftM f fs)  `addInfo` lPostl "myM1"-- [m1]
      ==== ((\f -> myLiftM f fs) ($ x))           `addInfo` beta-- beta-reduction
      ==== (myLiftM ($ x) fs )                    `addInfo` lFunc "myLiftM"-- myLiftM
      ==== (fs >>= return =. ($ x))               `addInfo` lFunc "=."-- (=.)
      ==== (fs >>= \f -> return ((=$ x) f))       `addInfo` lFunc "=$"-- ($)
      ==== (fs >>= \f -> return (f x))            `addInfo` beta)
{-
4 Applicative law (Composition)
return (.) <*>.. us <*>.. vs <*>.. xs  ==  us <*>.. (vs <*>.. xs)
-}
{- TODO ARI
    theoremApplicative4 :: Monad m => m (b -> c) -> m (a -> b) -> m a -> m c
    theoremApplicative4 us vs xs = value (
    ==== (return (=.) <*>.. us <*>.. vs <*>.. xs )         `addInfo` lPostl "lemma1"-- [lemma1]
    ==== (us >>= \u -> vs >>= \v -> myLiftM (u =. v) xs)   `addInfo` lPostl "lemma2"-- [lemma2]
    ==== (us <*>.. (vs <*>.. xs))                          `addInfo` beta)
    where
        lemma1 = value (-- left hand side transformation
        ==== (return (=.) <*>.. us <*>.. vs <*>.. xs )                              `addInfo` lFunc "myLiftM"-- (<*>..)
        ==== ((return (=.) >>= \c -> myLiftM c us) <*>.. vs <*>.. xs)               -- [m1]
        ==== ((\c -> myLiftM c us) (=.) <*>.. vs <*>.. xs)                          -- beta-reduction
        ==== (myLiftM (=.) us <*>.. vs <*>.. xs)                                    `addInfo` lFunc "myLiftM"-- myLiftM
        ==== ((us >>= return =. (=.)) <*>.. vs <*>.. xs)                            `addInfo` lFunc "myLiftM"-- (<*>..)
        ==== (((us >>= return =. (=.)) >>= \r -> myLiftM r vs) <*>.. xs)             -- [m3] 
        ==== ((us >>= \u -> (return =. (=.)) u >>= \r -> myLiftM r vs) <*>.. xs)    `addInfo` lFunc "myLiftM"-- (=.)
        ==== ((us >>= \u -> return (u =.) >>= \r -> myLiftM r vs) <*>.. xs)         -- [m1]
        ==== ((us >>= \u -> (\r -> myLiftM r vs) (u =.)) <*>.. xs)                  -- beta-reduction
        ==== ((us >>= \u -> myLiftM (u =.) vs) <*>.. xs)                            `addInfo` lFunc "myLiftM"-- myLiftM
        ==== ((us >>= \u -> vs >>= return =. (u =.)) <*>.. xs)                      `addInfo` lFunc "myLiftM"-- (<*>..)
        ==== ((us >>= \u -> vs >>= return =. (u =.)) >>= \f -> myLiftM f xs)         -- [m3] + beta-reduction ??????? TODO продумать многошаговость, если не вложенная, то, вроде, несложно
        ==== (us >>= \u -> vs >>= return =. (u =.) >>= \f -> myLiftM f xs)           -- [m3] 
        ==== (us >>= \u -> vs >>= \v -> (return =. (u =.)) v >>= \f -> myLiftM f xs) -- beta-reduction
        ==== (us >>= \u -> vs >>= \v -> return  (u =. v) >>= \f -> myLiftM f xs)    -- [m1]
        ==== (us >>= \u -> vs >>= \v ->  (\f -> myLiftM f xs) (u =. v))             -- beta-reduction
        ==== (us >>= \u -> vs >>= \v ->  myLiftM (u =. v) xs)                        `addInfo` beta)
        lemma2 = value (-- right hand side transformation
        ==== (us <*>.. (vs <*>.. xs) )                                -- (<*>..)
        ==== (us >>= \u -> myLiftM u (vs <*>.. xs))                     -- (<*>..)
        ==== (us >>= \u -> myLiftM u (vs >>= \v -> myLiftM v xs))         -- myLiftM
        ==== (us >>= \u -> (vs >>= \v -> myLiftM v xs) >>= return =. u)  -- [m3] + beta-reduction ??????
        ==== (us >>= \u -> vs >>= \v -> myLiftM v xs >>= return =. u)    -- myLiftM
        ==== (us >>= \u -> vs >>= \v -> myLiftM u (myLiftM v xs) )        -- [theoremFunctor2]
        ==== (us >>= \u -> vs >>= \v -> myLiftM (u =. v) xs)               `addInfo` beta)
-}

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
fishLeftNeutral k = value (
      (return >=> k)         `addInfo` lFunc ">=>" -- >=>
 ==== (\a -> return a >>= k) `addInfo` lPostl "myM1"-- [m1]
 ==== (\a -> k a)            `addInfo` lEta-- eta-reduction
 ==== k                      `addInfo` beta)

-- k >=> return  ==  k
fishRightNeutral :: Monad m => (a -> m b) -> a -> m b
fishRightNeutral k = value (
      (k >=> return)         `addInfo` lFunc ">=>"  -- >=>
 ==== (\a -> k a >>= return) `addInfo` lPostl "myM2"-- [m2]
 ==== (\a -> k a)            `addInfo` lEta-- eta-reduction
 ==== k                      `addInfo` beta)

-- (u >=> v) >=> w  ==  u >=> (v >=> w)
fishAssoc :: Monad m => (a -> m b) -> (b -> m c) -> (c -> m d) -> a -> m d
fishAssoc u v w = value (
      ((u >=> v) >=> w)                      `addInfo` lFunc ">=>"-- >=>
 ==== (\a -> (u >=> v) a >>= w)              `addInfo` lFunc ">=>"-- >=>
 ==== (\a -> (\a' -> u a' >>= v) a >>= w)    `addInfo` beta-- beta-reduction
 ==== (\a -> (u a >>= v) >>= w)              `addInfo` lPostl "myM3"-- [m3]
 ==== (\a -> u a >>= \b -> v b >>= w)        `addInfo` rFunc ">=>"-- >=>
 ==== (\a -> u a >>= (v >=> w))              `addInfo` rFunc ">=>"-- >=>
 ==== (u >=> (v >=> w))                      `addInfo` beta)

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
join x  =  x >>= myId 

--- (TODO если потом этим пользоваться как теоремой, то нужно научиться как-то экстрагировать отсюда эта-редуцированную версию)
--  join . return == id  -- :: m a -> m a
mjfr1 :: Monad m => m a -> m a
mjfr1 xs = value (
      ((join =. return) xs)   `addInfo` lFunc "=."-- (=.)
 ==== (join (return xs))      `addInfo` lFunc "join"-- join
 ==== ( return xs >>= myId)   `addInfo` lPostl "myM1"-- [m1]
 ==== ( myId xs)              `addInfo` lFunc "myId"-- myId
 ==== ( xs)                   `addInfo` beta) -- myId

---
--   join . fmap return == id  -- :: m a -> m a
mjfr2 :: Monad m => m a -> m a
mjfr2 xs = value (
     ((join =. myLiftM return) xs )               `addInfo` lFunc "=."-- (=.)
 ==== ( join (myLiftM return xs)  )                `addInfo` lFunc "join"-- join
 ==== ( myLiftM return xs >>= myId   )              `addInfo` lFunc "myLiftM" -- myLiftM
 ==== ( xs >>= return =. return >>= myId  )         `addInfo` lPostl "myM3"-- [m3]
 ==== ( xs >>= \x -> (return =. return) x >>= myId) `addInfo` lFunc "=."-- (=.)
 ==== ( xs >>= \x -> return (return x) >>= myId)   `addInfo` lPostl "myM1"-- [m1]
 ==== ( xs >>= \x -> myId (return x))              `addInfo` lFunc "myId"-- myId
 ==== ( xs >>= \x -> return x  )                 `addInfo` lEta-- eta-reduction
 ==== ( xs >>= return)                           `addInfo` lPostl "myM2"-- [m2]
 ==== ( xs      )                                `addInfo` rFunc "myId"-- myId
 ==== ( myId xs)                   `addInfo` beta) -- myId

---
--  join . fmap join  ==  join . join  -- :: m (m (m a)) -> m a
mjfr3 :: Monad m => m (m (m a)) -> m a
mjfr3 x3s = value (
     ((join =. myLiftM join) x3s  )                  `addInfo` lFunc "=."-- (=.)
 ==== ( join (myLiftM join x3s)     )                 `addInfo` lFunc "myLiftM"-- myLiftM
 ==== ( join (x3s >>= return =. join) )               `addInfo` lFunc "join"-- join
 ==== ( x3s >>= return =. join >>= myId )              `addInfo` lPostl "myM3"-- [m3]
 ==== ( x3s >>= \x2s -> (return =. join) x2s >>= myId) `addInfo` lFunc "=."-- (=.)
 ==== ( x3s >>= \x2s -> return (join x2s) >>= myId)   `addInfo` lPostl "myM1"-- [m1]
 ==== ( x3s >>= \x2s -> myId (join x2s))              `addInfo` lFunc "myId"-- myId
 ==== ( x3s >>= \x2s -> join x2s     )              `addInfo` lFunc "join"-- join
 ==== ( x3s >>= \x2s -> x2s >>= myId )                `addInfo` rFunc "myId"-- myId
 ==== ( x3s >>= \x2s -> myId x2s >>= myId )             `addInfo` lPostl "myM3"-- [m3]
 ==== ( x3s >>= myId >>= myId )                       `addInfo` rFunc "join"  -- join
 ==== ( join x3s >>= myId )                          `addInfo` rFunc "join" -- join
 ==== ( join (join x3s)   )                       `addInfo` rFunc "=." -- (=.)
 ==== ( (join =. join) x3s)                   `addInfo` beta) -- myId





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
--  === (\x -> k x >>= k') a         -- beta-reduction
--  === k a >>= k'                   -- inst (>>=) (1)
--  === (Just a >>= k) >>= k'
-- monad3LawMaybe Nothing k k' =
--      Nothing >>= \x -> k x >>= k' -- inst (>>=) (2)
--  === Nothing                      -- inst (>>=) (2)
--  === Nothing >>= k'               -- inst (>>=) (2)
--  === (Nothing >>= k) >>= k'          


-- flip (flip f) x y = f x y
-- a + b = b + a

-- 0 + a = a + 0
-- a + 0 = a

-- a + 0 = a = 0 + a

 -- Lists (TODO тут понадобятся гипотезы индукции, это второй этап)