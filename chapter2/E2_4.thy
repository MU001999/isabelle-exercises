theory E2_4
  imports Main
begin

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "snoc [] x = [x]" |
  "snoc (y # ys) x = y # (snoc ys x)"

fun reverse :: "'a list \<Rightarrow> 'a list" where
  "reverse [] = []" |
  "reverse (x # xs) = snoc (reverse xs) x"

value "reverse [1::nat, 2, 3, 4, 5]"

lemma reverse_02 [simp] : "reverse(snoc xs x) = x # (reverse xs)"
  apply(induction xs)
  apply(auto)
  done

(*
reverse (snoc (a # xs) x) = x # reverse (a # xs)
reverse (a # (snoc xs x)) = x # reverse (a # xs)
snoc (reverse (snoc xs x)) a = x # reverse (a # xs)
snoc (reverse (snoc xs x)) a = x # (snoc (reverse xs) a)
snoc (reverse (snoc xs x)) a = snoc (x # (reverse xs)) a
reverse (snoc xs x) = x # (reverse xs)
*)

lemma reverse_rr : "reverse (reverse xs) = xs"
  apply(induction xs)
  apply(auto)
  done

end
