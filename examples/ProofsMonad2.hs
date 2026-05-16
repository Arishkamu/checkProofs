module ProofsMonad2 where
import ProofBase
-- import Compose (composeAssoc, composeLeftNeutral)  -- Нужно только для пруфчекенга, живет в комментариях

import Prelude hiding ((.), id, ($), const, flip)

--------------------------------------------------------
class Functor m => AltMonad m where 
  ret :: a -> m a
  joi :: m (m a) -> m a

-- MonadLaws
{-
joi . ret       ==  id         -- (mjfr1)
joi . fmap ret  ==  id         -- (mjfr2)
joi . fmap joi  ==  joi . joi  -- (mjfr3)

fmap id         == id               -- (f1)
fmap (f . g)    ==  fmap f . fmap g -- (f2)
-}
-- postulates (это не доказывается, а является частью альтернативного определения монады)
mjfr1 :: AltMonad m => m a -> m a
mjfr1  =
     (joi . ret) --. Postulate
 === id          --. QED

mjfr2 :: AltMonad m => m a -> m a
mjfr2 =
     (joi . fmap ret)  --. Postulate
 === id                --. QED

mjfr3 :: AltMonad m => m (m (m a)) -> m a
mjfr3  = 
     (joi . fmap joi)  --. Postulate
 === (joi . joi)       --. QED

mjfr3Short :: AltMonad m => m (m (m a)) -> m (m a)
mjfr3Short  = 
     (fmap joi)  --. Postulate
 === (joi)       --. QED

f1 :: Functor m => m b -> m b
f1 = 
     fmap id   --. Postulate
 === id        --. QED

f2 :: Functor f => (b -> c) -> (a -> b) -> f a -> f c
f2 f g = 
     (fmap (f . g))     --. Postulate
 === (fmap f . fmap g)  --. QED

 {-
Выразите (>>=) через joi и fmap.
-}
bind :: AltMonad m => m a -> (a -> m b) ->  m b
--m >>=.. k = joi (fmap k m)
bind m k = (joi . fmap k) m


{-
Покажите, что законы класса типов Monad

ret a >>= k      ===  k a                     -- (m1)
m >>= ret        ===  m                       -- (m2)
(m >>= v) >>= w  ===  m >>= (\x -> v x >>= w) -- (m3)

следуют из законов 

joi . ret       ===  id         -- (mjfr1)
joi . fmap ret  ===  id         -- (mjfr2)
joi . fmap joi  ===  joi . joi  -- (mjfr3)

используя полученную ранее реализацию (>>=) через joi и fmap.

В преобразованиях можно использовать второй закон функторов

fmap (f . g)  =  fmap f . fmap g         -- (f2) 

и "свободные теоремы" для типов ret и joi

ret . f             = fmap f . ret   -- (FREE ret)
joi . fmap (fmap f) = fmap f . joi   -- (FREE joi)
-}

returnFREE :: Functor m => (forall a. a -> m a) -> (a -> b) -> a -> m b
returnFREE r f =  
     (fmap f . r) --. Postulate
 === (r . f)      --. QED

joinFREE :: Functor m => (forall a. m (m a) -> m a) -> (a -> b) -> m (m a) -> m b
joinFREE j f =  
     (j . fmap (fmap f))  --. Postulate
 === (fmap f . j)         --. QED

---
-- (m1)    ret a >>= k  ===  k a
m1'  :: AltMonad m => (a -> m b) -> a -> m b 
m1' k a = 
     (ret a `bind` k)           --. L (Def  "bind")
 === ((joi . fmap k) (ret a))   --. R (Def  ".")
 === (((joi . fmap k) . ret) a) --. Postulate -- [Compose.composeAssoc]
 === ((joi . (fmap k . ret)) a) --. L (Prop "returnFREE")
 === ((joi . (ret . k)) a)      --. Postulate -- [Compose.composeAssoc]
 === (((joi . ret) . k) a)      --. L (Prop "mjfr1")
 === ((id . k) a)               --. L (Def  ".")
 === (id (k a))                 --. L (Def  "id")
 === k a                        --. QED
---

-- (m2)    m >>= ret  ===  m 
m2'  :: AltMonad m => m a -> m a 
m2' m = 
     (m `bind` ret)        --. L (Def  "bind")
 === ((joi . fmap ret) m)  --. L (Prop "mjfr2")
 === id m                  --. L (Def  "id")
 === m                     --. QED
---
-- (m3)    (m >>= v) >>= w  ===  m >>= (\x -> v x >>= w)
m3' :: AltMonad m => m a -> (a -> m b) -> (b -> m c) -> m c
m3' m v w =
     (m `bind` v) `bind` w                         --. L (Def  "bind")
 === (joi . fmap w) (m `bind` v)                   --. L (Def  "bind")
 === (joi . fmap w) ((joi . fmap v) m)             --. R (Def  ".")
 === ((joi . fmap w) . joi . fmap v) m             --. Postulate-- [Compose.composeAssoc]
 === (joi . fmap w . joi . fmap v) m               --. Postulate-- [Compose.composeAssoc]
 === (joi . (fmap w . joi) . fmap v) m             --. R (Prop "joinFREE")
 === (joi . (joi . fmap (fmap w)) . fmap v) m      --. Postulate-- [Compose.composeAssoc]
 === (joi . joi . fmap (fmap w) . fmap v) m        --. Postulate-- [Compose.composeAssoc]
 === ((joi . joi) . fmap (fmap w) . fmap v) m      --. R (Prop "mjfr3Short")
 === ((joi . fmap joi) . fmap (fmap w) . fmap v) m --. Postulate-- [Compose.composeAssoc]
 === (joi . fmap joi . fmap (fmap w) . fmap v) m   --. R (Prop "f2")
 === (joi . fmap joi . fmap (fmap w . v)) m        --. R (Prop "f2")
 === (joi . fmap (joi . fmap w . v)) m             --. R (Def  "bind")
 === (m `bind` (joi . fmap w . v))                 --. R Eta
 === (m `bind` (\x -> (joi . fmap w . v) x))       --. Postulate
 === (m `bind` (\x -> ((joi . fmap w) . v) x))     --. Postulate-- [Compose.composeAssoc]
 === (m `bind` (\x -> (joi . fmap w) (v x)))       --. R (Def  "bind")
 === (m `bind` (\x -> v x `bind` w))               --. QED


----------------------------------------------------------------------------------------------
{-
Покажите, что рыбные законы класса типов Monad

ret >=> k        ===  k               -- (fish1)
k >=> ret        ===  k               -- (fish2)
(u >=> v) >=> w  ===  u >=> (v >=> w) -- (fish3)

следуют из законов 

joi . ret       ==  id         -- (mjfr1)
joi . fmap ret  ==  id         -- (mjfr2)
joi . fmap joi  ==  joi . joi  -- (mjfr3)

используя  реализацию (>=>) через fmap и joi.
-}

(>=>..) :: AltMonad m => (a -> m b) -> (b -> m c) -> a -> m c
g >=>.. h = joi . fmap h . g

---
-- (fish1)  ret >=> k  ===  k
fish1 :: AltMonad m => (a -> m b) -> a -> m b
fish1 k = 
     (ret >=>.. k)        --. L (Def  ">=>..")
 === (joi . fmap k . ret) --. L (Prop "returnFREE")
 === (joi . ret . k)      --. Postulate-- [Compose.composeAssoc]
 === ((joi . ret) . k)    --. L (Prop "mjfr1")
 === (id . k)             --. Postulate-- [Compose.composeLeftNeutral]
 === k                    --. QED
 --

-- (fish2)  k >=> ret  ===  k
fish2 :: AltMonad m => (a -> m b) -> a -> m b
fish2 k = 
     (k >=>.. ret)          --. L (Def  ">=>..")
 === (joi . fmap ret . k)   --. Postulate-- [Compose.composeAssoc]
 === ((joi . fmap ret) . k) --. L (Prop "mjfr2")
 === (id . k)               --. Postulate-- [Compose.composeLeftNeutral]
 === k                      --. QED
--

-- (fish3)  (u >=> v) >=> w  ===  u >=> (v >=> w)
fish3 :: AltMonad m => (a -> m b) -> (b -> m c) -> (c -> m d) -> a -> m d
fish3 u v w =
     ((u >=>.. v) >=>.. w)                           --. L (Def  ">=>..")
 === (joi . fmap w . (u >=>.. v))                    --. L (Def  ">=>..")
 === (joi . fmap w . joi . fmap v . u)               --. Postulate-- [Compose.composeAssoc]
 === (joi . (fmap w . joi) . fmap v . u)             --. R (Prop "joinFREE")
 === (joi . (joi . fmap (fmap w)) . fmap v . u)      --. Postulate-- [Compose.composeAssoc]
 === (joi . joi . fmap (fmap w) . fmap v . u)        --. Postulate-- [Compose.composeAssoc]
 === ((joi . joi) . fmap (fmap w) . fmap v . u)      --. R (Prop "mjfr3Short")
 === ((joi . fmap joi) . fmap (fmap w) . fmap v . u) --. Postulate-- [Compose.composeAssoc]
 === (joi . fmap joi . fmap (fmap w) . fmap v . u)   --. Postulate-- [Compose.composeAssoc]
 === (joi . fmap joi . (fmap (fmap w) . fmap v) . u) --. R (Prop "f2")
 === (joi . fmap joi . fmap ((fmap w) . v) . u)      --. Postulate-- [Compose.composeAssoc]
 === (joi . (fmap joi . fmap ((fmap w) . v)) . u)    --. R (Prop "f2")
 === (joi . fmap (joi . fmap w . v) . u)             --. R (Def  ">=>..")
 === (joi . fmap (v >=>.. w) . u)                    --. R (Def  ">=>..")
 === (u >=>.. (v >=>.. w))                           --. QED
-- mjfr3  = 
--      (joi . fmap joi) === (joi . joi)       --. QED

--------------------------------------------------
infixr 1 >==>
class MonadFish m where 
  retu :: a -> m a
  (>==>) :: (a -> m b) -> (b -> m c) -> a -> m c
-- postulates (это не доказывается, а является частью рыбного определения монады)
fLN :: MonadFish m => (b -> m c) -> b -> m c
fLN k =
     (retu >==> k) --. Postulate
 === k             --. QED

fLR :: MonadFish m => (a -> m c) -> a -> m c
fLR k =
     (k >==> retu) --. Postulate
 === k             --. QED

fAss :: MonadFish m => (a -> m b) -> (b -> m c) -> (c -> m d) -> a -> m d
fAss u v w =
     ((u >==> v) >==> w) --. Postulate
 === (u >==> (v >==> w)) --. QED


{-
Выразите (>>=), fmap, join  через  (>=>) и return.
-}

infixl 1 >>==
(>>==) :: MonadFish m => m a -> (a -> m b) -> m b
(>>==) m k = (id >==> k) m

fmap''' :: MonadFish m => (a -> b) -> m a -> m b
fmap''' f  = id >==> retu . f

join''' :: MonadFish m => m (m a) -> m a
join''' = id >==> id

{-
Покажите, что из рыбных законов 

retu >==> k       ===  k                   -- (fLN)
k >==> retu       ===  k                   -- (fRN)
(u >==> v) >=> w  ===  u >==> (v >==> w)   -- (fAss)

следуют законы класса типов Monad 

retu a >>== k        ===  k a                         -- (m1'')
m >>== retu          ===  m                           -- (m2'')
(m >>== k1) >>== k2  ===  m >>== (\x -> k1 x >>== k2) -- (m3'')

В преобразованиях понадобится "свободная теорема" для типа >=>

 (id >==> k2) . k1   ===   k1 >==> k2

-}

fishFREE :: MonadFish m => (a -> m b) -> (b -> m c) -> a -> m c
fishFREE k1 k2 = 
    ((id >==> k2) . k1)  --. Postulate
 === (k1 >==> k2)        --. QED

-- fishFREE :: (forall a b c. (a -> m b) -> (b -> m c) -> a -> m c) 
--                -> (a -> m b) -> (b -> m c) -> a -> m c
-- fishFREE c k1 k2 a = 
--      c k1 k2 a      --. Postulate
--  === c id k2 (k1 a) --. QED

-- return a >>== k   ===  k a
m1'' :: MonadFish m => a -> (a -> m b) -> m b
m1'' a k =
     (retu a >>== k)          --. L (Def  ">>==")
 === ((id >==> k) (retu a))   --. R (Def  ".")
 === (((id >==> k) . retu) a) --. L (Prop "fishFREE")
 === ((retu >==> k) a)        --. L (Prop "fLN")
 === k a                      --. QED

-- m >>== return  ===  m  
m2'' :: MonadFish m => m a -> m a
m2'' m =  
     (m >>== retu)      --. L (Def  ">>==")
 === ((id >==> retu) m) --. L (Prop "fLR")
 === id m               --. L (Def  "id")
 === m                  --. QED

-- (m >>== k1) >>== k2   ===   m >>== (\x -> k1 x >>== k2)
m3'' :: MonadFish m => m a -> (a -> m b) -> (b -> m c) -> m c
m3'' m k1 k2 = 
     ((m >>== k1) >>== k2)                --. L (Def  ">>==")
 === ((id >==> k1) m >>== k2)             --. L (Def  ">>==")
 === ((id >==> k2) ((id >==> k1) m))      --. R (Def  ".")
 === (((id >==> k2) . (id >==> k1)) m)    --. L (Prop "fishFREE") 
 === (((id >==> k1) >==> k2) m)           --. L (Prop "fAss")
 === ((id >==> (k1 >==> k2)) m)           --. R (Def  ">>==")
 === (m >>== (k1 >==> k2))                --. R (Prop "fishFREE")
 === (m >>== (id >==> k2) . k1)           --. L (Def  ".")
 === (m >>== (\x -> (id >==> k2) (k1 x))) --. R (Def  ">>==")
 === (m >>== (\x -> k1 x >>== k2))        --. QED

