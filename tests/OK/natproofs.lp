require open tests.OK.logic
require open tests.OK.bool
require open tests.OK.nat

// Symmetry of the equality (first option, rewrite).
theorem eq_sym : Πa x y, P (eq a x y) → P (eq a y x)
begin
  assume a x y h
  rewrite h
  refine refl a y
end

// Symmetry of the equality (second option, by hand).
theorem eq_sym_other_1 : Πa x y, P (eq a x y) → P (eq a y x)
begin
  assume a x y h
  refine eqind a x y h (λz, eq a y z) (refl a y)
end

// Symmetry of the equality (third option, by hand with a wildcard).
theorem eq_sym_other_2 : Πa x y, P (eq a x y) → P (eq a y x)
begin
  assume a x y h
  refine eqind a x y h (λz, eq a y z) _
  simpl
  refine refl a y
end

// [s] is compatible with Leibniz equality.
theorem s_eq : Πx y, P (eq nat x y) → P (eq nat (s x) (s y))
begin
  assume x y xy
  refine eqind nat x y xy (λz, eq nat (s z) (s y)) (refl nat (s y))
end

// [z] is right neutral for add.
theorem add0r : Πn, P (eq nat (n + 0) n)
begin
  // FIXME try to infer the predicate
  refine nat_ind (λn, eq _ (n + 0) n) ?CZ ?CS
  // Case Z
  simpl
  reflexivity
  // Case S
  assume n h
  simpl
  refine s_eq (add n 0) n h
end

// [Π n m, n + S m = S (n+m)]
theorem add_succ_r : Πn m, P (eq nat (n + (s m)) (s (n + m)))
begin
  assume n m
  refine nat_ind (λn, eq nat (n + (s m)) (s (n + m))) ?case_0 ?case_s n
  // Case Z
  simpl
  refine refl nat (s m)
  // Case S
  simpl
  assume pn ih
  rewrite ih
  simpl
  refine refl nat (s (s (pn + m)))
end

// Commutativity of the addition.
theorem addcomm : Πn m, P (eq nat (add n m) (add m n))
begin
  assume n m
  // FIXME try to infer nat
  refine nat_ind (λ n, eq nat (add n m) (add m n)) ?case_0 ?case_s n
  // Case Z
  simpl
  refine eq_sym _ (add m z) m (add0r m) // TODO add a symmetry tactic
  // Case S
  simpl
  assume k ih
  rewrite ih
  reflexivity
end

// Adding the same value is the same as multiplying by 2.
theorem add_same_times_two : Πx, P (eq nat (x + x) (2 × x))
begin
  assume x
  simpl
  refine refl nat (add x x)
end

//////////////////////////////////////////////////////////////////////////////
// Rewrite tests with quantified variables in the hypothesis.               //
//////////////////////////////////////////////////////////////////////////////

// This stupid test directly uses the addcomm lemma.
theorem rewriteTest1 : Πa b, P (eq nat (a + b) (b + a))
begin
  assume a b
  //print
  rewrite [add _ b] addcomm
  refine refl nat (add b a)
end

// This stupid test directly uses the addcomm lemma in one place.
theorem rewriteTest2 : Πa b, P (eq nat (a + b + b) (b + a + b))
begin
  assume a b
  //print
  rewrite [x in x + b] addcomm
  refine refl nat (b + a + b)
end

// This stupid test directly uses the addcomm lemma in two places.
theorem rewriteTest3 : Πa b,
  P (eq nat (add (add (add a b) b) (add (add a b) b))
            (add (add (add b a) b) (add (add b a) b)))
begin
  assume a b
  //print
  rewrite [x in (add x b)] addcomm
  refine refl nat (add (add (add b a) b) (add (add b a) b))
end

// An easy contextual rewrite.
theorem rewriteTest4 : Πa b,
  P (eq nat (add (add (add a b) (add a b)) a)
            (add (add (add b a) (add a b)) a))
begin
  assume a b
  rewrite [x in (add x (add a b))] addcomm
  refine refl nat (add (add (add b a) (add a b)) a)
end

// A slightly more complicated contextual rewrite.
theorem rewriteTest5 : Πa b,
  P (eq nat (add (add a b) (add a b)) (add (add b a) (add b a)))
begin
  assume a b
  rewrite [x in add x x] addcomm
  refine refl nat (add (add b a) (add b a))
end

// An even more complicated rewrite, combining both wildcards and binders.
theorem rewriteTest6 : Πa b,
  P (eq nat (add (add (add a b) a) a) (add (add a (add a b)) a))
begin
  // print
  assume a b
  rewrite [x in (add x _)] addcomm
  refine refl nat (add (add a (add a b)) a)
end

// Example 17: Very trivial SSReflect example.
symbol silly_axiom : Πm n, P (eq nat m n)

theorem rewriteTest7 : Πa b c,
 P (eq nat (add (add (add a b) c) (add a b))
           (add (add (add c b) c) (add a b)))
begin
  assume a b c
  rewrite [in x in (add x c)] (silly_axiom a c)
  refine refl nat (add (add (add c b) c) (add a b))
end

// Very trivial SSReflect example.
theorem rewriteTest8 : Πa b c,
 P (eq nat (add (add (add a b) c) (add a b))
           (add (add (add c b) c) (add a b)))
begin
  assume a b c
  rewrite [in (add (_) c)] (silly_axiom a c)
  refine refl nat (add (add (add c b) c) (add a b))
end

theorem rewriteTest9 : Πa b c,
  P (eq nat (add (add a b) (add c (add a b)))
            (add (add a b) (add c (add b a))))
begin
  assume a b c
  rewrite [(add a  _) in x in (add c x)] addcomm
  refine refl nat (add (add a b) (add c (add b a)))
end

theorem rewriteTest10 : Πa b c,
  P (eq nat (add (add c (add a b)) (add (add a b) (add c (add a b))))
            (add (add c (add b a)) (add (add a b) (add c (add b a)))))
begin
  assume a b c
  rewrite [(add a _) in x in (add c x)] addcomm
  refine refl nat (add (add c (add b a)) (add (add a b) (add c (add b a))))
end

theorem rewriteTest11 : Πa b c,
  P (eq nat (add (add (add (add a b) c) (add (add a b) c)) (add (add a b) c))
            (add (add (add (add a b) c) (add (add b a) c)) (add (add a b) c)))
begin
  assume a b c
  rewrite [(add a _) in x in (add (add _ x) _)] addcomm
  refine refl nat (add (add (add (add a b) c)
           (add (add b a) c)) (add (add a b) c))
end

theorem rewriteTest12 : Πa b c,
  P (eq nat (add (add c (add a b)) (add (add a b) (add c (add a b))))
            (add (add c (add b a)) (add (add a b) (add c (add b a)))))
begin
  assume a b c
  rewrite [(add a b) as x in (add _ x)] addcomm
  refine refl nat (add (add c (add b a)) (add (add a b) (add c (add b a))))
end
