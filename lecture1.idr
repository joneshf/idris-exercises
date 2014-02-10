module Lecture1

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
