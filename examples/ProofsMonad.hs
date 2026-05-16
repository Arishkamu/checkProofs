module ProofsMonad where
import ProofBase
-- import Compose (composeAssoc, composeLeftNeutral)  -- Нужно только для пруфчекенга, живет в комментариях

import Prelude hiding ((.), id, ($), const, flip, Monad(..), map, concat, foldr, (++))

------------------------------------------------------------------
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
  === (m >>= (return . f) . g)                      --. Postulate -- [Compose.composeAssoc]
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


-- {- AAAAA-3
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
-- AAAA-4 -}

 -- Lists (TODO тут понадобятся гипотезы индукции, это второй этап)

--  {-
instance Monad [] where
  (>>=) :: [a] -> (a -> [b]) -> [b]
  xs >>= k  =  concat (map k xs)
  
  return :: a -> [a]
  return a  =  a : []

-- определения функций над списками берем из Haskell Report 2010

map :: (a -> b) -> [a] -> [b]  
map f []     = []             -- (1)
map f (x:xs) = f x : map f xs -- (2)

concat :: [[a]] -> [a]  
concat xss = foldr (++) [] xss

foldr  :: (a -> b -> b) -> b -> [a] -> b  
foldr f z []     =  z                  -- (1)
foldr f z (x:xs) =  f x (foldr f z xs) -- (2)

(++) :: [a] -> [a] -> [a]  
[]     ++ ys = ys             -- (1)
(x:xs) ++ ys = x : (xs ++ ys) -- (2)
-- -}




{- AAAAA-1
-- forall xs . xs ++ [] === xs
lemmaAppendEmptyList :: [a] -> [a]
lemmaAppendEmptyList [] = 
     [] ++ []     --. L (Def  "++")
 === []           --. QED
lemmaAppendEmptyList (x:xs) = 
     (x:xs) ++ [] --. L (Def  "++")
 === x : xs ++ [] --. Postulate -- IH
 === x : xs       --. QED

 -- forall as bs cs . as ++ (bs ++ cs) === (as ++ bs) ++ cs 
lemmaAppendListAssoc :: [a] -> [a] -> [a] -> [a]
lemmaAppendListAssoc [] bs cs =
     [] ++ (bs ++ cs) --. L (Def  "++")
 === bs ++ cs         --. L (Def  "++")
 === ([] ++ bs) ++ cs --. QED
lemmaAppendListAssoc (a:as) bs cs =
     (a : as) ++ (bs ++ cs)  --. L (Def  "++")
 === a : as ++ (bs ++ cs)    --. Postulate -- IH
 === a : (as ++ bs) ++ cs    --. L (Def  "++")
 === (a : as ++ bs) ++ cs    --. L (Def  "++")
 === ((a : as) ++ bs) ++ cs  --. QED

 {- три полезные лемм -}
 
-- forall k. [] >>= k === []
lemmaBindEmptyList :: (a -> [b]) -> [b]
lemmaBindEmptyList k =
     [] >>= k          --. L (Inst ">>=")
 === concat (map k []) --. L (Def  "map")
 === concat []         --. L (Def  "concat")
 === foldr (++) [] []  --. L (Def  "foldr")
 === []                --. QED

-- forall x xs k. x : xs >>= k  ===  k x ++ (xs >>= k) 
lemmaBindNonEmptyList :: [a] -> (a -> [b]) -> [b]
lemmaBindNonEmptyList (x:xs) k =
     x : xs >>= k                    --. L (Inst ">>=")
 === concat (map k (x:xs))           --. L (Def  "map")
 === concat (k x : map k xs)         --. L (Def  "concat")
 === foldr (++) [] (k x : map k xs)  --. L (Def  "foldr")
 === k x ++ foldr (++) [] (map k xs) --. L (Def  "concat")
 === k x ++ concat (map k xs)        --. L (Inst ">>=")
 === k x ++ concat (map k xs)        --. L (Inst ">>=")
 === k x ++ (xs >>= k)               --. QED

-- forall as bs k. as ++ bs >>= k  ===  (as >>= k) ++ (bs >>= k) 
lemmaAppendDistribBindList :: [a] -> [a] -> (a -> [b]) -> [b]
lemmaAppendDistribBindList [] bs k =
     [] ++ bs >>= k             --. L (Def  "++")
 === bs >>= k                   --. L (Def  "++")
 === [] ++ (bs >>= k)           --. L (Prop "lemmaBindEmptyList")-- [lemmaBindEmptyList]
 === ([] >>= k) ++ (bs >>= k)   --. QED
lemmaAppendDistribBindList (a:as) bs k =
     (a : as) ++ bs >>= k              --. L (Def  "++")
 === a : as ++ bs >>= k                --. L (Prop "lemmaBindNonEmptyList")-- [lemmaBindNonEmptyList]
 === k a ++ (as ++ bs >>= k)           --. Postulate -- IH   
 === k a ++ ((as >>= k) ++ (bs >>= k)) --. L (Prop "lemmaAppendListAssoc")-- [lemmaAppendListAssoc]
 === (k a ++ (as >>= k)) ++ (bs >>= k) --. L (Prop "lemmaBindNonEmptyList")-- [lemmaBindNonEmptyList]
 === (a : as >>= k) ++ (bs >>= k)      --. QED

-- forall a k . return a >>= k === k a
monad1LawList :: a -> (a -> [b]) -> [b]
monad1LawList a k =
     return a >>= k           --. L (Inst "return")
 === a : [] >>= k             --. L (Inst ">>=")
 === concat (map k (a : []))  --. L (Def  "map")
 === concat (k a : map k [])  --. L (Def  "map")
 === concat (k a : [])        --. L (Def  "concat")
 === foldr (++) [] (k a : []) --. L (Def  "foldr")
 === k a ++ foldr (++) [] []  --. L (Def  "foldr")
 === k a ++ []                --. L (Prop "lemmaBindNonEmptyList")-- [lemmaAppendEmptyList]
 === k a                      --. QED

-- forall m . m >>= return === m  
monad2LawList :: [a] -> [a]
monad2LawList [] =
     [] >>= return --. L (Prop "lemmaBindEmptyList")-- [lemmaBindEmptyList]
 === []            --. QED
monad2LawList (x:xs) =
     x : xs >>= return           --  [lemmaBindNonEmptyList]
 === return x ++ (xs >>= return) -- IH
 === return x ++ xs              -- return
 === (x : []) ++ xs              --. L (Def  "++")
 === x : [] ++ xs                --. L (Def  "++")
 === x : xs

-- forall m k k' . m >>= k >>= k'  ===  m >>= \x -> k x >>= k'
monad3LawList ::  [a] -> (a ->[b]) -> (b -> [c]) -> [c]
monad3LawList [] k k' =
     [] >>= \x -> k x >>= k' -- [lemmaBindEmptyList]
 === []                      -- [lemmaBindEmptyList]
 === [] >>= k'               -- [lemmaBindEmptyList]
 === ([] >>= k) >>= k'
monad3LawList (x:xs) k k' =
     x : xs >>= \x -> k x >>= k'                       -- [lemmaBindNonEmptyList]
 === (\x -> k x >>= k') x ++ (xs >>= \x -> k x >>= k') --. L Beta
 === (k x >>= k') ++ (xs >>= \x -> k x >>= k')         -- IH
 === (k x >>= k') ++ ((xs >>= k) >>= k')               -- [lemmaAppendDistribBindList]
 === (k x ++ (xs >>= k)) >>= k'                        -- [lemmaBindNonEmptyList]
 === (x : xs >>= k) >>= k'

 -} -- AAAA2
