module Lecture1

infixl 4 <<*>>

total
repeat : (n : Nat) -> a -> Vect n a
repeat Z     _ = []
repeat (S n) a = a::repeat n a

total
vtake : (n : Nat) -> Vect (n + m) a -> Vect n a
vtake Z     _       = Nil
vtake (S n) (x::xs) = x::vtake n xs

total
vdrop : (n : Nat) -> Vect (n + m) a -> Vect m a
vdrop Z     vect    = vect
vdrop (S n) (_::xs) = vdrop n xs

Matrix : Nat -> Nat -> Type -> Type
Matrix m n a = Vect m (Vect n a)

twoByThree : Matrix 2 3 Int
twoByThree = [ [1,2,3]
             , [4,5,6]
             ]

threeByTwo : Matrix 3 2 Int
threeByTwo = [ [1,4]
             , [2,5]
             , [3,6]
             ]

fiveByFour : Matrix 5 4 Int
fiveByFour = [ [1,2,3,4]
             , [5,6,7,8]
             , [9,0,1,2]
             , [3,4,5,6]
             , [7,8,9,0]
             ]

fourByFive : Matrix 4 5 Int
fourByFive = [ [1,5,9,3,7]
             , [2,6,0,4,8]
             , [3,7,1,5,9]
             , [4,8,2,6,0]
             ]

transpose : Matrix m n a -> Matrix n m a
transpose []      = repeat _ []
transpose (x::xs) = zipWith (::) x (transpose xs)

(<<*>>) : Num a => Matrix m n a -> Matrix n r a -> Matrix m r a
[]      <<*>> b = []
(a::as) <<*>> b = (map (sum . zipWith (*) a) (transpose b)) :: (as <<*>> b)
