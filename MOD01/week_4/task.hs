
-- 4.12, 4.13, 4.14, 4.20, 4.21, 4.23, 4.24
import Test.QuickCheck
import GHC.Float (leDouble)
import Data.Binary.Get (Decoder(Fail))
import Data.List
-- import qualified Data.ByteString as
-- import Data.Char (ord)

-- -- 4.3

-- discr :: Double -> Double -> Double -> Double
-- discr a b c = b^2 - 4*a*c

-- root_1 :: Double -> Double -> Double -> Double
-- root_1 a b c 
--     | discr a b c < 0 = error "discriminant negative"
--     | otherwise = (-b + sqrt(discr a b c))/ 2*a 

-- root_2 :: Double -> Double -> Double -> Double
-- root_2 a b c 
--     | discr a b c < 0 = error "discriminant negative"
--     | otherwise = (-b - sqrt(discr a b c))/ 2*a 

-- -- 4.4

-- extrX :: Fractional a => a -> a -> p -> a
-- extrX a b c = -b / (2*a) 
-- extrY a b c = a*x^2 + b*x + c where x = extrX a b c

-- -- 4.5

-- isEnLower :: Char -> Bool
-- isEnLower x = ord x >= 97 

-- isEnUpper :: Char -> Bool
-- isEnUpper x = ord x <= 90

-- -- -- 4.6
-- import Test.QuickCheck

-- prop_total :: Int -> Property
-- prop_total n = (n >= 0) ==> total1 n == total2 n

-- total1 :: Int -> Int
-- total1 0 = 0
-- total1 n = total1 (n-1) + n
-- total2 :: Int -> Int
-- total2 n = -(n * (n+1)) `div` 2 


-- 4.7 
interest a p 0 = a 
interest a p n = (1+p)*interest a p (n-1)

-- 4.8

-- import Test.QuickCheck
-- prop_mylength xs = length xs == mylength xs
-- prop_mysum xs = mysum xs == sum xs
-- prop_myreverse xs = myreverse xs == reverse xs
-- prop_mytake n xs = n >= 0 ==> mytake n xs == take n xs
-- prop_myelem x ys = myelem x ys == elem x ys
-- prop_myconcat xs = myconcat xs == concat xs
-- prop_mymaximum xs = not (null xs) ==> mymaximum xs == maximum xs
-- prop_myzip xs ys = myzip xs ys == zip xs ys 

mylength ::[a] -> Int
mylength [] = 0
mylength (a:rest) = 1 + mylength (rest)

mysum :: Num a => [a] -> a
mysum [] = 0
-- mysum (a:[]) = a
mysum (a:rest) = a + mysum(rest)

myreverse :: [a] -> [a]
myreverse [] = []
myreverse (a:rest) = myreverse(rest) ++ a:[]

mytake :: Int -> [a] -> [a]
mytake n [] =[]
mytake 0 (a:rest) = []
mytake n (a:rest) 
    | n >= length(a:rest) = a:rest 
    | otherwise = a:(mytake (n-1) (rest))

myelem :: Eq t => t -> [t] -> Bool
myelem x [] = False
myelem x (a:rest) 
    | a == x = True
    | otherwise = myelem x (rest) 

myconcat :: [[a]] -> [a]
myconcat [] = []
myconcat (a:rest) = a ++ myconcat(rest)

mymaximum :: Ord a => [a] -> a
mymaximum [] = error "list empty"
mymaximum [a] = a
mymaximum (a : b : rest)
    | a > b = mymaximum (a:rest)
    | otherwise = mymaximum (b:rest) 

myzip :: [a] -> [a] -> [(a,a)]
myzip [][] = []
myzip [] (a1:rest1) = []
myzip (a:rest) [] = []
myzip (a:rest) (a1:rest1) = (a,a1):(myzip (rest) (rest1))

-- --4.9
r a d 0 = a
r a d i = d + r a d (i-1)

total_ a d i j 
    | j-i < 0 = 0
    | otherwise = r a d i + total_ a d (i+1) j

--4.10
allEqual [] = True
allEqual [a]= True
allEqual (a:b:rest) 
    | a == b = allEqual(b:rest)
    | otherwise = False

isASS [a] = []
isASS (a:b:rest) = (b-a):isASS(b:rest)
isAS [] = False
isAS [a] = True
isAS (a:b:rest) = allEqual (isASS(a:b:rest) )

--4.11
palindrome [] = True
palindrome (a:rest) = (a:rest) == myreverse(a:rest)



-- 4.15
incr :: Ord a => [a] -> Bool
incr [] = error "list empty"
incr [a] = True
incr (a:b:rest)
    | a < b = incr(b:rest)
    | otherwise = False

--4.16
contains [] [] = True
contains [] (b:rest1) = True
contains (a:rest) [] = False
contains (a:rest) (b:rest1) = myelem a (b:rest1) && contains (rest) (b:rest1)



contains1_ (a:rest) [] = []
contains1_ (a:rest) (b:rest1) 
    | myelem b (a:rest) = b: contains1_ (a:rest) (rest1)
    | otherwise = contains1_ (a:rest) (rest1)

contains1 [] [] = True
contains1 (a:rest) [] = False
contains1 [] (b:rest1) = True
contains1 (a:rest) (b:rest1) = (a:rest) == contains1_ (a:rest) (b:rest1)

--4.17
dividers n = [x | x <- [1..n], (n `mod` x) == 0 ]

--4.18
isPrime n = mylength(dividers n) == 2

--4.19
primeSum = [(x,y)| x<- [0..100], y <- [0..100], x+y == 100, isPrime x, isPrime y ]

-- 4.22

linsearch (a:rest) x = [ n1 | (n,n1) <- zip (a:rest) [0..mylength(a:rest)], n == x]

-- 4.25
ins x  [] = [x]
ins x (a:rest) 
    | x > a = a: ins x (rest)
    | otherwise = x:a:rest
isort [] = []
isort (a:rest) = ins a (isort(rest))

prop_isort xs= isort xs == sort xs
-- 4.26
merge [] [] = []
merge [] (b:restb) = (b:restb)
merge (a:rest) [] = (a:rest)
merge (a:rest) (b:restb)
    | a < b = a:merge rest (b:restb)
    | otherwise = b:merge restb (a:rest)

msort [] = []
msort [a] = [a]
msort (a:rest) = merge (msort fh) (msort sh) where (fh,sh) = splitAt (mylength (a:rest) `div` 2) (a:rest) 


-- 4.27
qsort [] = []
qsort [a] = [a]
qsort (a:rest) = (qsort [x| x<-(a:rest), x<a ])++[a]++ (qsort [x| x<-(a:rest), x>a] )

-- 4.28
itn f a 0 = a
itn f a n = f (itn f a (n-1))

-- 4.29

ins_h :: (a -> a -> Bool) -> a -> [a] -> [a]
ins_h r x  [] = [x]
ins_h r x (a:rest) 
    | x `r` a = x:a:rest
    | otherwise = a: ins_h r x (rest)

hoSort :: (a -> a -> Bool) -> [a] -> [a]
hoSort r [] = []
hoSort r (a:rest) =  ins_h r a (hoSort r (rest))

prop_hoSort :: [Int] -> Bool
prop_hoSort xs= hoSort (<) xs == sort xs

-- 4.30
dice_0 = [(x,y)| x <- [1..6], y <- [1..6]]
dice_1 n = [(x,y)| x <- [1..6], y <- [1..6], (x == n) || ( y==n)]
dice_2 m = [(x,y)| x <- [1..6], y <- [1..6], x+y == m]

dice_3 :: [(Integer, Integer)]
dice_3 = hoSort (\(x,x1) (a,a1) ->(x+x1) < (a+a1)) [(x,y)| x <- [1..6], y <- [1..6]]