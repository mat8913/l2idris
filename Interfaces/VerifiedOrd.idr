module Interfaces.VerifiedOrd

import Data.Fin

%default total
%access public export

typeOf : (x : a) -> Type
typeOf {a} x = a

reverseOrd : Ordering -> Ordering
reverseOrd EQ = EQ
reverseOrd LT = GT
reverseOrd GT = LT

orderPair : Ordering -> Ordering -> Ordering
orderPair EQ x = x
orderPair x  _ = x

data DecOrd : Ordering -> Type where
  IsEQ : (o = EQ) -> DecOrd o
  IsLT : (o = LT) -> DecOrd o
  IsGT : (o = GT) -> DecOrd o

decOrd : (o : Ordering) -> DecOrd o
decOrd EQ = IsEQ Refl
decOrd GT = IsGT Refl
decOrd LT = IsLT Refl

decOrdEq : (o : Ordering) -> Dec (o = EQ)
decOrdEq EQ = Yes Refl
decOrdEq LT = No (\Refl impossible)
decOrdEq GT = No (\Refl impossible)

interface VerifiedOrd a where
  order : a -> a -> Ordering
  ordRefl : (x : a) -> order x x = EQ
  reflOrd : (x : a) -> (y : a) -> order x y = EQ -> x = y
  ordSym  : (x : a) -> (y : a) -> order x y = reverseOrd (order y x)
  ordTrans : (left : a) -> (middle : a) -> (right : a) -> order left middle = order middle right -> order left middle = order left right

ordRefl' : VerifiedOrd a => (x : a) -> (y : a) -> (x = y) -> order x y = EQ
ordRefl' x x Refl = ordRefl x

decEqVerifiedOrd : VerifiedOrd a => (x : a) -> (y : a) -> Dec (x = y)
decEqVerifiedOrd x y with (decOrdEq (order x y))
  | Yes p = Yes $ reflOrd x y p
  | No  p = No  $ \xeqy => p $ ordRefl' x y xeqy

implementation VerifiedOrd () where
  order = compare
  ordRefl () = Refl
  reflOrd () () _ = Refl
  ordSym () () = Refl
  ordTrans () () () _ = Refl

implementation VerifiedOrd Bool where
  order = compare
  ordRefl True = Refl
  ordRefl False = Refl
  reflOrd True True _ = Refl
  reflOrd True False Refl impossible
  reflOrd False True Refl impossible
  reflOrd False False _ = Refl
  ordSym True True = Refl
  ordSym True False = Refl
  ordSym False True = Refl
  ordSym False False = Refl
  ordTrans False False False _ = Refl
  ordTrans True True True _ = Refl
  ordTrans False False True Refl impossible
  ordTrans False True False Refl impossible
  ordTrans True False False Refl impossible
  ordTrans False True True Refl impossible
  ordTrans True False True Refl impossible
  ordTrans True True False Refl impossible

pair_ordTrans_lemma1 : (VerifiedOrd a, VerifiedOrd b) =>
                       {l1, m1, r1 : a} ->
                       {l2, m2, r2 : b} ->
                       (order l1 m1 = GT) ->
                       (order m1 r1 = LT) ->
                       (orderPair (order l1 m1) (order l2 m2) = orderPair (order m1 r1) (order m2 r2)) ->
                       Void
pair_ordTrans_lemma1 p1 p2 = rewrite p1 in rewrite p2 in \Refl impossible

pair_ordTrans_lemma2 : (VerifiedOrd a, VerifiedOrd b) =>
                       {l1, m1, r1 : a} ->
                       {l2, m2, r2 : b} ->
                       (order l1 m1 = LT) ->
                       (order m1 r1 = GT) ->
                       (orderPair (order l1 m1) (order l2 m2) = orderPair (order m1 r1) (order m2 r2)) ->
                       Void
pair_ordTrans_lemma2 p1 p2 = rewrite p1 in rewrite p2 in \Refl impossible

pair_ordTrans_lemma3 : (VerifiedOrd a, VerifiedOrd b) =>
                       (l1 : a) ->
                       (m1 : a) ->
                       (r1 : a) ->
                       (l2 : b) ->
                       (m2 : b) ->
                       (r2 : b) ->
                       (order l1 m1 = EQ) ->
                       (order m1 r1 = EQ) ->
                       (orderPair (order l1 m1) (order l2 m2) = orderPair (order m1 r1) (order m2 r2)) ->
                       (order l2 m2 = order m2 r2)
pair_ordTrans_lemma3 _ _ _ _ _ _ p1 p2 = rewrite p1 in rewrite p2 in \x => x

pair_ordTrans_lemma4 : (VerifiedOrd a, VerifiedOrd b) =>
                       (l1 : a) ->
                       (m1 : a) ->
                       (r1 : a) ->
                       (l2 : b) ->
                       (m2 : b) ->
                       (r2 : b) ->
                       (order l1 m1 = EQ) ->
                       (order m1 r1 = LT) ->
                       (orderPair (order l1 m1) (order l2 m2) = orderPair (order m1 r1) (order m2 r2)) ->
                       (order l2 m2 = LT)
pair_ordTrans_lemma4 _ _ _ _ _ _ p1 p2 = rewrite p1 in rewrite p2 in \x => x

pair_ordTrans_lemma5 : (VerifiedOrd a, VerifiedOrd b) =>
                       (l1 : a) ->
                       (m1 : a) ->
                       (r1 : a) ->
                       (l2 : b) ->
                       (m2 : b) ->
                       (r2 : b) ->
                       (order l1 m1 = EQ) ->
                       (order m1 r1 = GT) ->
                       (orderPair (order l1 m1) (order l2 m2) = orderPair (order m1 r1) (order m2 r2)) ->
                       (order l2 m2 = GT)
pair_ordTrans_lemma5 _ _ _ _ _ _ p1 p2 = rewrite p1 in rewrite p2 in \x => x

implementation (VerifiedOrd a, VerifiedOrd b) => VerifiedOrd (a, b) where
  order (x1, x2) (y1, y2) = orderPair (order x1 y1) (order x2 y2)
  ordRefl (x1, x2) = rewrite ordRefl x1 in ordRefl x2
  reflOrd (x1, x2) (y1, y2) p with (decOrdEq (order x1 y1))
    | Yes p2 with (reflOrd x1 y1 p2)
      reflOrd (x1, x2) (x1, y2) p | Yes p2 | Refl with (order x1 x1)
        | EQ = rewrite reflOrd x2 y2 p in Refl
        reflOrd (_, _) (_, _) Refl | Yes _ | Refl | LT impossible
        reflOrd (_, _) (_, _) Refl | Yes _ | Refl | GT impossible
    | No p2 with (order x1 y1)
      reflOrd (_, _) (_, _) Refl | No _ | GT impossible
      reflOrd (_, _) (_, _) Refl | No _ | LT impossible
      | EQ = void $ p2 Refl
  ordSym (x1, x2) (y1, y2) with (decOrd (order y1 x1))
    | IsEQ p = rewrite ordSym x1 y1 in rewrite p in ordSym x2 y2
    | IsLT p = rewrite ordSym x1 y1 in rewrite p in Refl
    | IsGT p = rewrite ordSym x1 y1 in rewrite p in Refl
  ordTrans (l1, l2) (m1, m2) (r1, r2) p with (decOrd (order l1 m1))
    | IsLT p1 with (decOrd (order m1 r1))
      | IsLT p2 = rewrite sym (ordTrans l1 m1 r1 (trans p1 (sym p2))) in rewrite p1 in Refl
      | IsGT p2 = void $ pair_ordTrans_lemma2 {l1=l1} {l2=l2} {m1=m1} {m2=m2} {r1=r1} {r2=r2} p1 p2 p
      | IsEQ p2 with (reflOrd m1 r1 p2)
        ordTrans (l1, l2) (m1, m2) (m1, r2) p | IsLT p1 | IsEQ _ | Refl with (order l1 m1)
          ordTrans (_, _) (_, _) (_, _) _ | IsLT Refl | IsEQ _ | Refl | EQ impossible
          | LT = Refl
          | GT = Refl
    | IsGT p1 with (decOrd (order m1 r1))
      | IsGT p2 = rewrite sym (ordTrans l1 m1 r1 (trans p1 (sym p2))) in rewrite p1 in Refl
      | IsLT p2 = void $ pair_ordTrans_lemma1 {l1=l1} {l2=l2} {m1=m1} {m2=m2} {r1=r1} {r2=r2} p1 p2 p
      | IsEQ p2 with (reflOrd m1 r1 p2)
        ordTrans (l1, l2) (m1, m2) (m1, r2) p | IsGT p1 | IsEQ _ | Refl with (order l1 m1)
          ordTrans (_, _) (_, _) (_, _) _ | IsGT Refl | IsEQ _ | Refl | EQ impossible
          | LT = Refl
          | GT = Refl
    | IsEQ p1 with (decOrd (order m1 r1))
        | IsEQ p2 = rewrite p1 in rewrite sym (ordTrans l1 m1 r1 (trans p1 (sym p2))) in rewrite p1 in ordTrans l2 m2 r2 (pair_ordTrans_lemma3 l1 m1 r1 l2 m2 r2 p1 p2 p)
        | IsLT p2 = rewrite p1 in rewrite reflOrd l1 m1 p1 in rewrite p2 in pair_ordTrans_lemma4 l1 m1 r1 l2 m2 r2 p1 p2 p
        | IsGT p2 = rewrite p1 in rewrite reflOrd l1 m1 p1 in rewrite p2 in pair_ordTrans_lemma5 l1 m1 r1 l2 m2 r2 p1 p2 p

implementation VerifiedOrd a => VerifiedOrd (List a) where
  order []      []      = EQ
  order []      (_::_)  = LT
  order (_::_)  []      = GT
  order (x::xs) (y::ys) = orderPair (order x y) (order xs ys)
  ordRefl [] = Refl
  ordRefl (x::xs) = rewrite ordRefl x in ordRefl xs
  reflOrd [] [] _ = Refl
  reflOrd (x::xs) (y::ys) p with (decOrdEq (order x y))
    | Yes p2 with (reflOrd x y p2)
      reflOrd (x::xs) (x::ys) p | Yes p2 | Refl with (order x x)
        reflOrd (x::xs) (x::ys) p | Yes p2   | Refl | EQ = rewrite reflOrd xs ys p in Refl
        reflOrd (_::_)  (_::_)  _ | Yes Refl | Refl | LT impossible
        reflOrd (_::_)  (_::_)  _ | Yes Refl | Refl | GT impossible
    | No p2 with (order x y)
      | EQ = void $ p2 Refl
      | LT = void $ p2 p
      | GT = void $ p2 p
  reflOrd [] (_::_) Refl impossible
  reflOrd (_::_) [] Refl impossible
  ordSym [] [] = Refl
  ordSym [] (_::_) = Refl
  ordSym (_::_) [] = Refl
  ordSym (x::xs) (y::ys) with (decOrd (order x y))
    | IsLT p = rewrite ordSym y x in rewrite p in Refl
    | IsGT p = rewrite ordSym y x in rewrite p in Refl
    | IsEQ p = rewrite ordSym y x in rewrite p in ordSym xs ys
  ordTrans [] [] zs p = p
  ordTrans [] (y::ys) (z::zs) p = Refl
  ordTrans (x::xs) (y::ys) [] p = p
  ordTrans (x::xs) (y::ys) (z::zs) p with (decOrd (order x y))
    | IsLT p1 with (decOrd (order y z))
      | IsLT p2 = rewrite sym (ordTrans x y z (trans p1 (sym p2))) in rewrite p1 in Refl
      | IsGT p2 = void $ (the (typeOf p -> Void) (rewrite p1 in rewrite p2 in \Refl impossible)) p
      | IsEQ p2 = rewrite (sym (reflOrd y z p2)) in rewrite p1 in Refl
    | IsGT p1 with (decOrd (order y z))
      | IsGT p2 = rewrite sym (ordTrans x y z (trans p1 (sym p2))) in rewrite p1 in Refl
      | IsLT p2 = void $ (the (typeOf p -> Void) (rewrite p1 in rewrite p2 in \Refl impossible)) p
      | IsEQ p2 = rewrite (sym (reflOrd y z p2)) in rewrite p1 in Refl
    | IsEQ p1 with (decOrd (order y z))
      | IsEQ p2 = the (typeOf p -> order (x::xs) (y::ys) = order (x::xs) (z::zs)) (rewrite sym (reflOrd y z p2) in rewrite reflOrd x y p1 in rewrite ordRefl y in ordTrans xs ys zs) p
      | IsGT p2 = rewrite p1 in rewrite (reflOrd x y p1) in rewrite p2 in (the (typeOf p -> order xs ys = GT) (rewrite p1 in rewrite p2 in id)) p
      | IsLT p2 = rewrite p1 in rewrite (reflOrd x y p1) in rewrite p2 in (the (typeOf p -> order xs ys = LT) (rewrite p1 in rewrite p2 in id)) p
  ordTrans [] (_::_) [] Refl impossible
  ordTrans (_::_) [] [] Refl impossible
  ordTrans (_::_) [] (_::_) Refl impossible

implementation VerifiedOrd Nat where
  order = compare
  ordRefl Z = Refl
  ordRefl (S n) = ordRefl n
  reflOrd Z Z _ = Refl
  reflOrd Z (S _) Refl impossible
  reflOrd (S _) Z Refl impossible
  reflOrd (S n) (S m) p = cong (reflOrd n m p)
  ordSym Z Z = Refl
  ordSym Z (S _) = Refl
  ordSym (S _) Z = Refl
  ordSym (S m) (S n) = ordSym m n
  ordTrans Z Z Z _ = Refl
  ordTrans Z (S m) (S r) _ = Refl
  ordTrans (S l) (S m) Z p = p
  ordTrans (S l) (S m) (S r) p = ordTrans l m r p
  ordTrans Z Z (S r) Refl impossible
  ordTrans Z (S m) Z Refl impossible
  ordTrans (S l) Z Z Refl impossible
  ordTrans (S l) Z (S r) Refl impossible

implementation VerifiedOrd (Fin n) where
  order = compare
  ordRefl FZ = Refl
  ordRefl (FS n) = ordRefl n
  reflOrd FZ FZ _ = Refl
  reflOrd (FS n) (FS m) p = cong $ reflOrd n m p
  reflOrd FZ (FS _) Refl impossible
  reflOrd (FS _) FZ Refl impossible
  ordSym FZ FZ = Refl
  ordSym FZ (FS _) = Refl
  ordSym (FS _) FZ = Refl
  ordSym (FS m) (FS n) = ordSym m n
  ordTrans FZ FZ FZ _ = Refl
  ordTrans FZ (FS m) (FS r) _ = Refl
  ordTrans (FS l) (FS m) FZ p = p
  ordTrans (FS l) (FS m) (FS r) p = ordTrans l m r p
  ordTrans FZ FZ (FS r) Refl impossible
  ordTrans FZ (FS m) FZ Refl impossible
  ordTrans (FS l) FZ FZ Refl impossible
  ordTrans (FS l) FZ (FS r) Refl impossible
