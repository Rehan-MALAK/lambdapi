require open tests.test4
theorem eq_sym : Πa x y, P (eq a x y) → P (eq a y x)
begin
  assume a x y h
  rewrite h
  refine refl a y
end
