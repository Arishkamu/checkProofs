module ExampleInstGood where

-- import ProofBase (importThisFunc)
import ProofBase hiding (importThisFuncHiding)

res4 :: a -> b -> (a, String)
res4 a b = (\x y -> (x, importThisFuncHiding y)) (importThisFunc a) b

importThisFuncHiding :: a -> String
importThisFuncHiding _ = "AAAA"