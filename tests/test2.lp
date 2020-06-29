constant symbol nat : TYPE
constant symbol n0 : nat
constant symbol nS : nat → nat

theorem n1 : nat
begin
  solve
  refine nS n0
end
