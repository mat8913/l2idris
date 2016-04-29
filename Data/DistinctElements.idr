module Data.DistinctElements

import public Data.Vect
import public Data.Function

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

elemSplit : Elem x (y::xs) -> Either (x=y) (Elem x xs)
elemSplit Here {x = y} {y = y} {xs = xs} = Left Refl
elemSplit (There later) {x = x} {y = y} {xs = xs} = Right later

equalityElem : x=y -> Elem x (y::xs)
equalityElem Refl {x = x} {y = x} = Here

reduceNotElem : Not (Elem x (y::xs)) -> Not (Elem x xs)
reduceNotElem p Here {x = x} {xs = xs} impossible
reduceNotElem p (There _) {x = x} {xs = xs} impossible

notElemMapInjective : Injective f -> DistinctElements xs -> Not (Elem x xs) -> Elem (f x) (Prelude.Functor.map f xs) -> Void
notElemMapInjective inj p ne el {x} {xs=[]} = absurd el
notElemMapInjective inj (p,ps) ne el {f} {x} {xs=(y::xs)} = case elemSplit el of
    Left p2 => ne (equalityElem (inj p2))
    Right p2 => notElemMapInjective inj ps (reduceNotElem ne) p2

mapInjectiveFunction : Injective f -> DistinctElements xs -> DistinctElements (Prelude.Functor.map f xs)
mapInjectiveFunction inj p {f} {xs = []} = p
mapInjectiveFunction inj (p, ps) {f} {xs = (x::xs)} = (notElemMapInjective inj ps p, mapInjectiveFunction inj ps)
