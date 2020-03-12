theory E3_2
  imports Main
begin

inductive palindromes :: "'a list \<Rightarrow> bool" where
pp0 : "palindromes []" |
pp1 : "palindromes [x]" |
ppn : "palindromes xs \<Longrightarrow> palindromes (a # xs @ [a])"

lemma "palindromes xs \<Longrightarrow> rev xs = xs"
  apply(induction xs rule : palindromes.induct)
  by auto

end
