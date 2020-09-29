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
// print
//   assume a
// print
//   assume ea 
// print
//   apply ea 
// qed
symbol trivial : Π A , eU A → eU A ≔
begin
  print
  solve
  print
  assume a
  print
  assume ea
  print
  apply ea
end
