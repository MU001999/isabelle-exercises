theory E3_3
  imports Main
begin

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl : "star r x x" |
step : "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

inductive star' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl' : "star' r x x" |
step' : "star' r x y \<Longrightarrow> r y z \<Longrightarrow> star' r x z"

lemma star1 [simp, intro] : "star r x y \<Longrightarrow> r y z \<Longrightarrow> star r x z"
  apply (induction rule : star.induct)
  apply (meson star.simps)
  by (simp add: star.step)

lemma star'1 [simp, intro] : "star' r y z \<Longrightarrow> r x y \<Longrightarrow> star' r x z"
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
