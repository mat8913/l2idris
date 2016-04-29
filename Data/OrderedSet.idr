module Data.OrderedSet

import public Data.DistinctElements

%access public export
%default total

data OrderedSet : Nat -> Type -> Type where
    FromVect : (xs : Vect n a) -> {auto p : DistinctElements xs} -> OrderedSet n a

Elem : a -> OrderedSet n a -> Type
Elem x (FromVect xs) = Elem x xs

Nil : OrderedSet Z a
Nil = FromVect []

(::) : (x : a) -> (xs : OrderedSet n a) -> {default absurd p : Not (Elem x xs)} -> OrderedSet (S n) a
(::) x (FromVect xs {p = ps}) {p = p} = FromVect (x::xs) {p = (p,ps)}

tail : OrderedSet (S n) a -> OrderedSet n a
tail (FromVect (_ :: xs) {p = (_, ps)}) = FromVect xs

isElem : DecEq a => (x : a) -> (xs : OrderedSet n a) -> Dec (Elem x xs)
isElem x (FromVect xs) = isElem x xs

toVect : OrderedSet n a -> Vect n a
toVect (FromVect xs) = xs

map : {f : a -> b} -> Injective f -> OrderedSet n a -> OrderedSet n b
map inj (FromVect xs {p}) {f} = FromVect (map f xs) {p = mapInjectiveFunction inj p}
