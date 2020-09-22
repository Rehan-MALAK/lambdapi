constant symbol U : TYPE
injective symbol eU : U → TYPE
// set flag "eta_equality" on // default is off
// set flag "print_implicits" on // default is off
// set flag "print_contexts" on // default is off
// set flag "print_domains" on // default is off
set flag "print_meta_type" on // default is off
set verbose 3
set debug +u
// theorem trivial : Π A, eU A → eU A
// proof
//   // solve
//   print
//   assume a
//   print
//   assume p_a
//   print
//   apply p_a
//   print
// qed
symbol trivial : Π A, eU A → eU A ≔
begin
  print
  assume a
  assume ea
  apply ea
//   focus 2
//   print
//   assume a
//   print
//   focus 1
//   print
//   assume ea
//   print
//   focus 1
//   print
//   apply ea
//   print
//   solve
//   print
// //   assume a
//   print
//   focus 3
//   print
//   assume ea
//   print
end
