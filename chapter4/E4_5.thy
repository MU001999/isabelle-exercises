theory E4_5
  imports Main
begin

inductive star :: "('a ⇒ 'a ⇒ bool) ⇒ 'a ⇒ 'a ⇒ bool" for r where
refl : "star r x x" |
step : "r x y ⟹ star r y z ⟹ star r x z"

inductive iter :: "('a ⇒ 'a ⇒ bool) ⇒ nat ⇒ 'a ⇒ 'a ⇒ bool" for r where
iter0 : "iter r n x x" |
iter1 : "r x y ⟹ iter r 1 x y ⟹ iter r n y z ⟹ iter r (n + 1) x z" |
iter2 : "iter r n x y ⟹ r y z ⟹ iter r (n + 1) x z" |
iter3 : "iter r n x y ⟹ iter r m y z ⟹ iter r (m + n) x z"

lemma star_trans[simp, intro] : "star r x y ⟹ star r y z ⟹ star r x z"
proof (induction rule : star.induct)  
  case (refl x)
  thus ?case by auto
next
  case (step x y z)
  thus ?case by (meson star.step)
qed

lemma "iter r n x y ⟹ star r x y"
proof (induction rule : iter.induct)
  case (iter0 n x)
  then show ?case by (meson star.simps)
next
  case (iter1 x y n z)
  then show ?case by blast
next
  case (iter2 n x y z)
  then show ?case by (meson star.refl star.step star_trans)
next
  case (iter3 n x y m z)
  then show ?case by blast
qed

end
