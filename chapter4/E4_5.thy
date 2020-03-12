theory E4_5
  imports Main
begin

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl : "star r x x" |
step : "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
iter0 : "iter r n x x" |
iter1 : "r x y \<Longrightarrow> iter r 1 x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (n + 1) x z" |
iter2 : "iter r n x y \<Longrightarrow> r y z \<Longrightarrow> iter r (n + 1) x z" |
iter3 : "iter r n x y \<Longrightarrow> iter r m y z \<Longrightarrow> iter r (m + n) x z"

lemma star_trans[simp, intro] : "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
proof (induction rule : star.induct)
  case (refl x)
  thus ?case by auto
next
  case (step x y z)
  thus ?case by (meson star.step)
qed

lemma "iter r n x y \<Longrightarrow> star r x y"
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
