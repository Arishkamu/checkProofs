module ForDiploma where

simpleFunction :: Show a => (a, String) -> String
simpleFunction (n, todo) = show n ++ ": " ++ todo

-- simpleFunction :: a -> a
-- simpleFunction x = x