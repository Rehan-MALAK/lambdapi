constant symbol unit : TYPE
constant symbol tt : unit
constant symbol U : TYPE
constant symbol un : U

symbol eU : U → TYPE
rule eU un ↪ unit

constant symbol piU : Π (x : U), Π (_ : eU x → U), U
rule eU (piU $X $Y) ↪ Π (x : eU $X), eU ($Y x)

theorem myfirstbegin : Π (A : U), eU A → eU A
begin
  assume A
  assume eU_A
  apply eU_A
end
