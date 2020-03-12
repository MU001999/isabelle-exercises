theory E3_4
  imports Main
begin

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl : "star r x x" |
step : "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

lemma star1 [simp, intro] : "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
  apply (induction rule : star.induct)
  apply (assumption)
  by (metis step)

lemma star2 [simp, intro] : "r y z \<Longrightarrow> star r y z"
  by (meson star.simps)

lemma star3 [simp, intro] : "star r x y \<Longrightarrow> r y z \<Longrightarrow> star r x z"
  apply (induction rule : star.induct)
  apply (meson star.simps)
  by auto

inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
iter0 : "iter r n x x" |
iter1 : "r x y \<Longrightarrow> iter r 1 x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (n + 1) x z" |
iter2 : "iter r n x y \<Longrightarrow> r y z \<Longrightarrow> iter r (n + 1) x z" |
iter3 : "iter r n x y \<Longrightarrow> iter r m y z \<Longrightarrow> iter r (m + n) x z"

lemma "star r x y \<Longrightarrow> \<exists> n. iter r n x y"
  apply (induction rule : star.induct)
  apply (simp add : iter0)
  by (metis test.iter.simps)

end
