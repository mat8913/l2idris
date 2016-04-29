module Data.DistinctElements

import public Data.Vect

%access public export
%default total

DistinctElements : Vect n a -> Type
DistinctElements [] = ()
DistinctElements (x :: xs) = (Not (Elem x xs), DistinctElements xs)

isDistinctElements : DecEq a => (xs : Vect n a) -> Dec (DistinctElements xs)
isDistinctElements [] = Yes ()
isDistinctElements (x :: xs) with (isElem x xs)
    | Yes p = No (\(f, _) => f p)
    | No p1 with (isDistinctElements xs)
        | Yes p2 = Yes (p1,p2)
        | No  p2 = No (\(_, d) => p2 d)
