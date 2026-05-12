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
L Beta-reduction    -- применена или контрпременена эта-редукция

liftM             -- применено или контрпременено определение функции (NB должно быть доступно)
foldr (2)         -- применено или контрпременено определение функции (с уточнением конкретного равенства в определении) 

[theoremFunctor1] -- применена или контрпременена теорема

{POSTULATE}       -- не пруфчекаем переход, верим на слово

inst return       -- применено или контрпременено определение реализации метода представителя для класса типов 
                  -- (TODO надо ли указывать для какого типа? Или это всегда выводится?)


-}


data SideExprInfo = L ExprInfo | R ExprInfo | QED

-- lFunc str = L (Func str)
-- rFunc str = R (Func str)
-- lPostl str = L (Postl str)
-- rPostl str = R (Postl str)
-- L Eta = L Eta
-- R Eta = R Eta
-- L Beta = L Beta

data ExprInfo = Func String | Postl String | Beta | Eta
-- data WithInfo a = WithInfo { value :: a, info :: SideExprInfo}

(--.) :: a -> SideExprInfo -> a
(--.) x _ = x

postulate :: a -> a -> a
postulate = const

infixl 0 ===
(===) :: a -> a -> a
(===) x y = y


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
composeAssoc4 f g h =
    (f =. (g =. h))                   --. L (Func "=.")
 === (\x -> f ((g =. h) x))          --. L (Func "=.")
 === (\x -> f ((\x' -> g (h x')) x)) --. L Beta
 === (\x -> f (g (h x)))             --. L Beta
 === (\x -> (\x' -> f (g x')) (h x)) --. R (Func "=.")
 === (\x -> (f =. g) (h x))          --. R (Func "=.")
 === ((f =. g) =. h)                 --. QED


composeLeftNeutral :: (a -> b) -> a -> b
composeLeftNeutral f =
      (myId =. f)           --. L (Func "=.")
 === (\x -> myId (f x))    --. L (Func "myId")
 === (\x -> f x)           --. L Eta
 === f                     --. QED

composeRightNeutral :: (a -> b) -> a -> b
composeRightNeutral f =
      (f =. myId)        --. L (Func "=.")
 === (\x -> f (myId x)) --. L (Func "myId")
 === (\x -> f x)        --. L Eta
 === f                  --. QED


flipFlipIsId :: (a -> b -> c) -> a -> b -> c
flipFlipIsId  =
     (myFlip =. myFlip)                         --. L (Func "=.")
 === (\f -> myFlip (myFlip f))                 --. R Eta
 === (\f -> \x -> myFlip (myFlip f) x)         --. R Eta
 === (\f -> \x -> \y -> myFlip (myFlip f) x y) --. L (Func "myFlip")
 === (\f -> \x -> \y -> myFlip f y x)          --. L (Func "myFlip")
 === (\f -> \x -> \y -> f x y)                 --. L Eta
 === (\f -> \x -> f x)                         --. L Eta
 === (\f -> f)                                 --. R (Func "myId")
 === (\f -> myId f)                            --. L Eta
 === myId                                      --. QED

{- forall f x y. myFlip (myFlip f) x y === f x y -}
flipFlipIsId' :: (a -> b -> c) -> a -> b -> c
flipFlipIsId' f x y =
      myFlip (myFlip f) x y  --. L (Func "myFlip")
 === myFlip f y x           --. L (Func "myFlip")
 === f x y                  --. QED






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
theoremFunctor1 xs =
  (myLiftM myId xs)                      --. L (Func "myLiftM")
  === (xs >>= return =. myId)           --. L (Func "=.")
  === (xs >>= \x -> return (myId x))  --. L (Func "myId")
  === (xs >>= \x -> return x)         --. L Eta
  === (xs >>= return)                 --. L (Postl "myM2")
  === xs                              --. QED
{-
2 Functor law
liftM (f . g) xs == liftM f (liftM g xs)
-}
theoremFunctor2 :: Monad m => (b -> c) -> (a -> b) -> m a -> m c
theoremFunctor2 f g xs =
       (myLiftM f (myLiftM g xs))                     --. L (Func "myLiftM")-- liftM
  === (myLiftM f (xs >>= return =. g))               --. L (Func "myLiftM")-- liftM
  === ((xs >>= return =. g) >>= return =. f)         --. L (Postl "myM3")-- [m3]
  === (xs >>= \x -> (return =. g) x >>= return =. f) --. L (Func "=.")-- (.)
  === (xs >>= \x -> return (g x) >>= return =. f)    --. L (Postl "myM1")-- [m1]
  === (xs >>= \x -> (return =. f) (g x))             --. R (Func "=.")-- (.)
  === (xs >>= \x -> ((return =. f) =. g) x)          --. L Eta-- eta-reduction
  === (xs >>= (return =. f) =. g)                    --. R (Postl "composeAssoc4")-- assoc (.) ?????????
  === (xs >>= return =. (f =. g))                    --. R (Func "myLiftM")-- liftM
  === (myLiftM (f =. g) xs)                          --. QED

-- f =. (g =. h) === (f =. g) =. h

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
theoremApplicative0 g xs =
       (return g <*>.. xs)                --. L (Func "<*>..")-- (<*>..)
  === (return g >>= \f -> myLiftM f xs)  --. L (Postl "myM1")-- [m1]
  === ((\f -> myLiftM f xs) g)           --. L Beta-- L Beta-reduction
  === (myLiftM g xs)                     --. QED

{-
1 Applicative law (Identity)
return id <*>.. xs  == xs
-}
theoremApplicative1 :: Monad m => m b -> m b
theoremApplicative1 xs =
       (return myId <*>.. xs)                 --. L (Func "<*>..")-- (<*>..)
  === (return myId >>= \f -> myLiftM f xs)   --. L (Postl "myM1")-- [m1]
  === ((\f -> myLiftM f xs) myId)            --. L Beta-- L Beta-reduction
  === (myLiftM myId xs)                      --. L (Postl "theoremFunctor1")-- [theoremFunctor1]
  === xs                                     --. QED

{-
2 Applicative law (Homomorphism)
return g <*>.. return x  == return (g x)
-}
theoremApplicative2 :: Monad m => (a -> b) ->  a -> m b
theoremApplicative2 g x =
       (return g <*>.. return x)                 --. L (Func "<*>..")-- (<*>..)
  === (return g >>= \f -> myLiftM f (return x)) --. L (Postl "myM1")-- [m1]
  === ((\f -> myLiftM f (return x)) g)          --. L Beta-- L Beta-reduction
  === (myLiftM g (return x))                    --. L (Func "myLiftM")-- myLiftM
  === (return x >>= return =. g)                --. L (Postl "myM1")-- [m1]
  === ((return =. g) x )                        --. L (Func "=.")-- (=.)
  === (return (g x))                             --. QED

{-
3 Applicative law (Interchange)
fs <*>.. return x  ===  return ($ x) <*>.. fs
-}
theoremApplicative3 :: Monad m => m (a -> b) -> a -> m b
theoremApplicative3 fs x =
       (fs <*>.. return x )         --. L  (Postl "lemma1")-- [lemma1]
  === (fs >>= \f -> return (f x))  --. R (Postl "lemma2")-- [lemma2]
  === (return (=$ x) <*>.. fs)      --. QED


lemma1 fs x = -- L hand side transformation
        (fs <*>.. return x )                     --. L (Func "<*>..")-- (<*>..)
    === (fs >>= \f -> myLiftM f (return x))      --. L (Func "myLiftM") -- myLiftM
    === (fs >>= \f -> return x >>= return =. f)  --. L (Postl "myM1")-- [m1]
    === (fs >>= \f -> (return =. f) x )          --. L (Func "=.")-- (=.)
    === (fs >>= \f -> return (f x))              --. QED

lemma2 fs x = -- R hand side transformation
        (return (=$ x) <*>.. fs)                --. L (Func "<*>..")-- (<*>..)
    === (return (=$ x) >>= \f -> myLiftM f fs)  --. L (Postl "myM1")-- [m1]
    === ((\f -> myLiftM f fs) (=$ x))           --. L Beta-- L Beta-reduction
    === (myLiftM (=$ x) fs )                    --. L (Func "myLiftM")-- myLiftM
    === (fs >>= return =. (=$ x))               --. L (Func "=.")-- (=.)
    === (fs >>= \f -> return ((=$ x) f))       --. L (Func "=$")-- ($)
    === (fs >>= \f -> return (f x))            --. QED

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
      (return (=.) <*>.. us <*>.. vs <*>.. xs )      --. L (Postl "ta4_lemma1")-- [lemma1]
 === (us >>= \u -> vs >>= \v -> myLiftM (u =. v) xs) --. R (Postl "ta4_lemma2")-- [lemma2]
 === (us <*>.. (vs <*>.. xs))                        --. QED

ta4_lemma1 :: Monad m => m (b -> c) -> m (a -> b) -> m a -> m c
ta4_lemma1 us vs xs = -- L hand side transformation
      (return (=.) <*>.. us <*>.. vs <*>.. xs )                              --. L (Func "<*>..")-- (<*>..)
 === ((return (=.) >>= \c -> myLiftM c us) <*>.. vs <*>.. xs)               --. L (Postl "myM1")-- [m1]
 === ((\c -> myLiftM c us) (=.) <*>.. vs <*>.. xs)                          --. L Beta-- L Beta-reduction
 === (myLiftM (=.) us <*>.. vs <*>.. xs)                                    --. L (Func "myLiftM")-- myLiftM
 === ((us >>= return =. (=.)) <*>.. vs <*>.. xs)                            --. L (Func "<*>..")-- (<*>..)
 === (((us >>= return =. (=.)) >>= \r -> myLiftM r vs) <*>.. xs)            --. L (Postl "myM3")-- [m3] 
 === ((us >>= \u -> (return =. (=.)) u >>= \r -> myLiftM r vs) <*>.. xs)    --. L (Func "=.")-- (=.)
 === ((us >>= \u -> return (u =.) >>= \r -> myLiftM r vs) <*>.. xs)         --. L (Postl "myM1")-- [m1]
 === ((us >>= \u -> (\r -> myLiftM r vs) (u =.)) <*>.. xs)                  --. L Beta-- L Beta-reduction
 === ((us >>= \u -> myLiftM (u =.) vs) <*>.. xs)                            --. L (Func "myLiftM")-- myLiftM
 === ((us >>= \u -> vs >>= return =. (u =.)) <*>.. xs)                      --. L (Func "<*>..")-- (<*>..)
 === ((us >>= \u -> vs >>= return =. (u =.)) >>= \f -> myLiftM f xs)         --. L (Postl "myM3")
--  === ((us >>= \u -> vs >>= return =. (u =.)) >>= \f -> myLiftM f xs)         --. L Beta-- [m3] + L Beta-reduction ??????? TODO продумать многошаговость, если не вложенная, то, вроде, несложно
 === (us >>= \u -> vs >>= return =. (u =.) >>= \f -> myLiftM f xs)           --. L (Postl "myM3")-- [m3] 
 === (us >>= \u -> vs >>= \v -> (return =. (u =.)) v >>= \f -> myLiftM f xs) --. L (Func "=.")-- L Beta-reduction
 === (us >>= \u -> vs >>= \v -> return  (u =. v) >>= \f -> myLiftM f xs)     --. L (Postl "myM1")-- [m1]
 === (us >>= \u -> vs >>= \v ->  (\f -> myLiftM f xs) (u =. v))              --. L Beta-- L Beta-reduction
 === (us >>= \u -> vs >>= \v ->  myLiftM (u =. v) xs)                        --. QED

-- -- myM3 m k k' = (m >>= k >>= k')  `postulate`  (m >>= \x -> k x >>= k')

ta4_lemma2 :: Monad m => m (b -> c) -> m (a -> b) -> m a -> m c
ta4_lemma2 us vs xs = -- R hand side transformation
      (us <*>.. (vs <*>.. xs) )                                   --. L (Func "<*>..")-- (<*>..)
 === (us >>= \u -> myLiftM u (vs <*>.. xs))                      --. L (Func "<*>..")-- (<*>..)
 === (us >>= \u -> myLiftM u (vs >>= \v -> myLiftM v xs))        --. L (Func "myLiftM") -- myLiftM
 === (us >>= \u -> (vs >>= \v -> myLiftM v xs) >>= return =. u)  --. L (Postl "myM3")-- [m3] + L Beta-reduction ??????
--  === (us >>= \x -> (\u -> (vs >>= \v -> myLiftM v xs)) x >>= return =. u)  -- [m3] + L Beta-reduction ??????
 === (us >>= \u -> vs >>= \v -> myLiftM v xs >>= return =. u)    --. R (Func "myLiftM")-- myLiftM
 === (us >>= \u -> vs >>= \v -> myLiftM u (myLiftM v xs) )       --. L (Postl "theoremFunctor2") -- [theoremFunctor2]
 === (us >>= \u -> vs >>= \v -> myLiftM (u =. v) xs)             --. QED

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
      (return >=> k)         --. L (Func ">=>") -- >=>
 === (\a -> return a >>= k) --. L (Postl "myM1")-- [m1]
 === (\a -> k a)            --. L Eta-- eta-reduction
 === k                      --. QED

-- k >=> return  ==  k
fishRightNeutral :: Monad m => (a -> m b) -> a -> m b
fishRightNeutral k =
      (k >=> return)         --. L (Func ">=>")  -- >=>
 === (\a -> k a >>= return) --. L (Postl "myM2")-- [m2]
 === (\a -> k a)            --. L Eta-- eta-reduction
 === k                      --. QED

-- (u >=> v) >=> w  ==  u >=> (v >=> w)
fishAssoc :: Monad m => (a -> m b) -> (b -> m c) -> (c -> m d) -> a -> m d
fishAssoc u v w =
      ((u >=> v) >=> w)                      --. L (Func ">=>")-- >=>
 === (\a -> (u >=> v) a >>= w)              --. L (Func ">=>")-- >=>
 === (\a -> (\a' -> u a' >>= v) a >>= w)    --. L Beta-- L Beta-reduction
 === (\a -> (u a >>= v) >>= w)              --. L (Postl "myM3")-- [m3]
 === (\a -> u a >>= \b -> v b >>= w)        --. R (Func ">=>")-- >=>
 === (\a -> u a >>= (v >=> w))              --. R (Func ">=>")-- >=>
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
join x  =  x >>= myId 

--- (TODO если потом этим пользоваться как теоремой, то нужно научиться как-то экстрагировать отсюда эта-редуцированную версию)
--  join . return == id  -- :: m a -> m a
mjfr1 :: Monad m => m a -> m a
mjfr1 xs =
      ((join =. return) xs)   --. L (Func "=.")-- (=.)
 === (join (return xs))      --. L (Func "join")-- join
 === ( return xs >>= myId)   --. L (Postl "myM1")-- [m1]
 === ( myId xs)              --. L (Func "myId")-- myId
 === ( xs)                   --. QED -- myId

---
--   join . fmap return == id  -- :: m a -> m a
mjfr2 :: Monad m => m a -> m a
mjfr2 xs =
     ((join =. myLiftM return) xs )                 --. L (Func "=.")-- (=.)
 === ( join (myLiftM return xs)  )                 --. L (Func "join")-- join
 === ( myLiftM return xs >>= myId   )              --. L (Func "myLiftM") -- myLiftM
 === ( xs >>= return =. return >>= myId  )         --. L (Postl "myM3")-- [m3]
 === ( xs >>= \x -> (return =. return) x >>= myId) --. L (Func "=.")-- (=.)
 === ( xs >>= \x -> return (return x) >>= myId)    --. L (Postl "myM1")-- [m1]
 === ( xs >>= \x -> myId (return x))               --. L (Func "myId")-- myId
 === ( xs >>= \x -> return x  )                    --. L Eta-- eta-reduction
 === ( xs >>= return)                              --. L (Postl "myM2")-- [m2]
 === ( xs      )                                   --. R (Func "myId")-- myId
 === ( myId xs)                                    --. QED -- myId

---
--  join . fmap join  ==  join . join  -- :: m (m (m a)) -> m a
mjfr3 :: Monad m => m (m (m a)) -> m a
mjfr3 x3s =
     ((join =. myLiftM join) x3s  )                    --. L (Func "=.")-- (=.)
 === ( join (myLiftM join x3s)     )                  --. L (Func "myLiftM")-- myLiftM
 === ( join (x3s >>= return =. join) )                --. L (Func "join")-- join
 === ( x3s >>= return =. join >>= myId )              --. L (Postl "myM3")-- [m3]
 === ( x3s >>= \x2s -> (return =. join) x2s >>= myId) --. L (Func "=.")-- (=.)
 === ( x3s >>= \x2s -> return (join x2s) >>= myId)    --. L (Postl "myM1")-- [m1]
 === ( x3s >>= \x2s -> myId (join x2s))               --. L (Func "myId")-- myId
 === ( x3s >>= \x2s -> join x2s     )                 --. L (Func "join")-- join
 === ( x3s >>= \x2s -> x2s >>= myId )                 --. R (Func "myId")-- myId
 === ( x3s >>= \x2s -> myId x2s >>= myId )            --. L (Postl "myM3")-- [m3]
 === ( x3s >>= myId >>= myId )                        --. R (Func "join")  -- join
 === ( join x3s >>= myId )                            --. R (Func "join") -- join
 === ( join (join x3s)   )                            --. R (Func "=.") -- (=.)
 === ( (join =. join) x3s)                            --. QED -- myId





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