constant symbol unit : TYPE
constant symbol tt : unit
constant symbol U : TYPE
constant symbol un : U

symbol eU : U ⇒ TYPE
rule eU un → unit

constant symbol piU : ∀ (x : U), ∀ (_ : eU x ⇒ U), U
rule eU (piU &X &Y) → ∀ (x : eU &X), eU (&Y x)

theorem myfirstproof : ∀ (A : U), eU A ⇒ eU A
proof
    assume A
    assume proof_of_A
    apply proof_of_A
qed