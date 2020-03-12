theory E3_4
  imports Main
begin

inductive star :: "('a ⇒ 'a ⇒ bool) ⇒ 'a ⇒ 'a ⇒ bool" for r where
refl : "star r x x" |
step : "r x y ⟹ star r y z ⟹ star r x z"

lemma star1 [simp, intro] : "star r x y ⟹ star r y z ⟹ star r x z"
  apply (induction rule : star.induct)
  apply (assumption)
  by (metis step)

lemma star2 [simp, intro] : "r y z ⟹ star r y z"
  by (meson star.simps)

lemma star3 [simp, intro] : "star r x y ⟹ r y z ⟹ star r x z"
  apply (induction rule : star.induct)
  apply (meson star.simps)
  by auto

inductive iter :: "('a ⇒ 'a ⇒ bool) ⇒ nat ⇒ 'a ⇒ 'a ⇒ bool" for r where
iter0 : "iter r n x x" |
iter2 : "r x y ⟹ iter r 1 x y ⟹ iter r n y z ⟹ iter r (n + 1) x z" |
iter3 : "iter r n x y ⟹ r y z ⟹ iter r (n + 1) x z" |
iter4 : "iter r n x y ⟹ iter r m y z ⟹ iter r (m + n) x z"

lemma "star r x y ⟹ ∃ n. iter r n x y"
  apply (induction rule : star.induct)
  apply (simp add : iter0)
  by (metis test.iter.simps)

end
