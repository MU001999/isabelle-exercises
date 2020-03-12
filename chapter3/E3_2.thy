theory E3_2
  imports Main
begin

inductive palindromes :: "'a list ⇒ bool" where
pp0 : "palindromes []" |
pp1 : "palindromes [x]" |
ppn : "palindromes xs ⟹ palindromes (a # xs @ [a])"

lemma "palindromes xs ⟹ rev xs = xs"
  apply(induction xs rule : palindromes.induct)
  by auto

end
