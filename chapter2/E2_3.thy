theory E2_3
  imports Main
begin

fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "count x [] = 0" |
  "count x (y # xs) = If (x = y) (Suc (count x xs)) (count x xs)"

value "count (1::nat) [1, 2, 3, 1, 3, 1]"

lemma count_lt : "count x xs \<le> length xs"
  apply(induction xs)
  apply(auto)
  done

end
