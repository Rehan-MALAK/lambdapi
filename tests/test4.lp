constant symbol U : TYPE
injective symbol T : U → TYPE
constant symbol Prop : TYPE
constant symbol all : Π (a : U), (T a → Prop) → Prop

injective symbol P : Prop → TYPE
rule P (all $a $f) ↪ Π (x : T $a), P ($f x)

constant symbol eq : Πa, T a → T a → Prop
constant symbol refl  : Πa x, P (eq a x x)
constant symbol eqind : Πa x y, P (eq a x y) → Π (p:T a→Prop), P (p y) → P (p x)

set builtin "P"     ≔ P
set builtin "T"     ≔ T
set builtin "eq"    ≔ eq
set builtin "eqind" ≔ eqind
set builtin "refl"  ≔ refl
