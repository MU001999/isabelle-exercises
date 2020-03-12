theory E4_1
  imports Main
begin

lemma assumes T: "∀ x y. T x y ∨ T y x"
  and A: "∀ x y. A x y ∧ A y x ⟶ x = y"
  and TA: "∀ x y. T x y ⟶ A x y" and "A x y"
  shows "T x y"
proof -
  from T A TA `A x y` show "T x y" by blast
qed

end
