theory E3_5
  imports Main
begin

datatype alpha = a | b

inductive S :: "alpha list \<Rightarrow> bool" where
S0 : "S []" |
S1 : "S w \<Longrightarrow> S (a # w @ [b])" |
S2 : "S w \<Longrightarrow> S v \<Longrightarrow> S (w @ v)"

inductive T :: "alpha list \<Rightarrow> bool" where
T0 : "T []" |
T1 : "T w \<Longrightarrow> T v \<Longrightarrow> T (w @ [a] @ v @ [b])"

lemma T_cat [simp] : "T v \<Longrightarrow> T w \<Longrightarrow> T (w @ v)"
  apply (induction rule : T.induct)
  apply simp
  by (metis T.simps append.assoc)

lemma "S w = T w"
  apply (rule)
  apply (induction rule : S.induct)
  apply (rule T0)
  apply auto
  apply (metis T.simps append_Cons append_Nil)
  apply (induction rule : T.induct)
  apply (rule S0)
  by (simp add: S1 S2)

end
