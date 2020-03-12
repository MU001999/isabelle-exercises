theory E3_5
  imports Main
begin

datatype alpha = a | b

inductive S :: "alpha list ⇒ bool" where
S0 : "S []" |
S1 : "S w ⟹ S (a # w @ [b])" |
S2 : "S w ⟹ S v ⟹ S (w @ v)"

inductive T :: "alpha list ⇒ bool" where
T0 : "T []" |
T1 : "T w ⟹ T v ⟹ T (w @ [a] @ v @ [b])"

lemma T_cat [simp] : "T v ⟹ T w ⟹ T (w @ v)"
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
