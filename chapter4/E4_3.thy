theory E4_3
  imports Main
begin

inductive ev :: "nat ⇒ bool" where
ev0 : "ev 0" |
evSS : "ev n ⟹ ev (Suc (Suc n))"

lemma assumes a: "ev (Suc (Suc n))" shows "ev n"
proof -
  from a show ?thesis
  proof cases
    case ev0
  next
    case evSS
    thus ?thesis by auto
  qed
qed
