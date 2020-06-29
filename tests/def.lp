constant symbol unit : TYPE
constant symbol f : (unit → unit) → unit

theorem g1 : unit
begin
  refine f (λx,x)
end
