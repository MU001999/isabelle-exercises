theory E3_3
  imports Main
begin

inductive star :: "('a ⇒ 'a ⇒ bool) ⇒ 'a ⇒ 'a ⇒ bool" for r where
refl : "star r x x" |
step : "r x y ⟹ star r y z ⟹ star r x z"

inductive star' :: "('a ⇒ 'a ⇒ bool) ⇒ 'a ⇒ 'a ⇒ bool" for r where
refl' : "star' r x x" |
step' : "star' r x y ⟹ r y z ⟹ star' r x z"

lemma star1 [simp, intro] : "star r x y ⟹ r y z ⟹ star r x z"
  apply (induction rule : star.induct)
  apply (meson star.simps)
  by (simp add: star.step)

lemma star'1 [simp, intro] : "star' r y z ⟹ r x y ⟹ star' r x z"
  apply (induction rule : star'.induct)
  apply (meson refl' step')
  by (simp add: step')

lemma res1 [simp] : "star' r x y = star r x y"
  apply rule
  apply (induction rule : star'.induct)
  apply (meson star.simps)
  apply auto
  apply (induction rule : star.induct)
  apply (meson star'.simps)
  by auto

end
