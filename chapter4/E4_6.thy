theory E4_6
  imports Main
begin

fun elems :: "'a list ⇒ 'a set" where
  "elems [] = {}" |
  "elems (x # xs) = {x} ∪ elems xs"

lemma "x ∈ elems xs ⟹ ∃ ys zs. xs = ys @ x # zs ∧ x ∉ elems ys"
proof (induction xs)
case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case 
  proof (cases "x = a")
    case True
    then show ?thesis by fastforce
  next
    case False
    hence "x ∈ elems xs" using Cons.prems by auto 
    thus ?thesis by (metis Cons.IH False UnE append_Cons elems.simps(2) empty_iff insert_iff)
  qed
qed

end
