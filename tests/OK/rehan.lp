constant symbol A : TYPE
constant symbol f : A → TYPE ≔ λ_,A
// definition f : A → TYPE ≔ λ_,A
constant symbol g : Πx, f x ≔
begin
  refine λy,y
end
// theorem g : Πx, f x
// proof
//   refine λy,y
// qed
