module Data.Function

%access public export
%default total

Inverse : (f : a -> b) -> (g : b -> a) -> Type
Inverse f g = (g . f) = Prelude.Basics.id

Involution : (f : a -> a) -> Type
Involution f = (f . f) = Prelude.Basics.id

Injective : (f : a -> b) -> Type
Injective f {a} {b} = {x : a} -> {y : a} -> (f x = f y) -> (x = y)

Surjective : (g : a -> b) -> Type
Surjective g = Exists (\f => Inverse f g)

Bijective : (f : a -> b) -> Type
Bijective f = (Injective f, Surjective f)

applyId : (f = Prelude.Basics.id) -> (f x = f y) -> (x = y)
applyId p = rewrite p in id

hasInverseIsInjective : Inverse f g -> Injective f
hasInverseIsInjective p1 p2 {g} = applyId p1 (cong p2 {f=g})

inverseIsSurjective : Inverse f g -> Surjective g
inverseIsSurjective p {f} = Evidence f p

involutionIsBijective : Involution f -> Bijective f
involutionIsBijective inv = (hasInverseIsInjective inv, inverseIsSurjective inv)

inverseOfComposition : Inverse f invF -> Inverse g invG -> Inverse (f . g) (invG . invF)
inverseOfComposition pf pg {g} {invF} {invG} =
    let p = cong (cong pf {f=(. g)}) {f=(invG .)}
        in rewrite sym pg
            in p

uniqueInverse : Surjective f -> Inverse f g -> Inverse f h -> g = h
uniqueInverse (Evidence inv p) invG invH {f} {g} {h} = trans gInv hInv
  where
    gInv : g = inv
    gInv = trans (sym (cong p {f=(g .)})) (cong invG {f=(. inv)})
    hInv : inv = h
    hInv = trans (sym (cong invH {f=(. inv)})) (cong p {f=(h .)})

inverseSymmetry : Surjective f -> Inverse f g -> Inverse g f
inverseSymmetry (Evidence val p) invF {f} {g} = solution
  where
    step1 : g . f . val = g
    step1 = cong p {f=(g .)}
    step2 : g . f . val = val
    step2 = cong invF {f=(. val)}
    step3 : g = val
    step3 = trans (sym step1) step2
    solution : Inverse g f
    solution = rewrite step3 in p
