constant symbol unit : TYPE
constant symbol tt : unit
constant symbol U : TYPE
constant symbol un : U

symbol eU : U → TYPE
rule eU un ↪ unit

// MASTER
// [/home/jean/travail/ocaml/lambdapi/tests/test.lp, 20:5-21] Cannot solve eU ?12 ≡ unit.
// Cannot solve eU ?12 ≡ unit.
// Cannot infer the type of [f (λx, x)].

// UNIF_HINT
// set unif_rule (eU $x) ≡ unit ↪ $x ≡ un
// ...
// (infr) f (λx, x) : U

constant symbol f : (unit → unit) → U

definition g ≔ f (λx, x)
// definition g ≔ f (λx : eU _, x)
// begin
//   unifrule (eU $x) ≡ unit ↪ $x ≡ un
//   refine f (λx : eU _ ,x)
// end
