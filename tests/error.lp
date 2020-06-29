constant symbol nat : TYPE
constant symbol n0 : nat
constant symbol nS : nat → nat
definition n1 ≔ nS n0

constant symbol F : nat → TYPE
constant symbol T0 : F n0
constant symbol T1 : F n1

definition T2 : F n1 ≔ T0
begin
  solve
end
