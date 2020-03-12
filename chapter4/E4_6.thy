theory E4_6
  imports Main
begin

fun elems :: "'a list \<Rightarrow> 'a set" where
  "elems [] = {}" |
  "elems (x # xs) = {x} \<union> elems xs"

lemma "x \<in> elems xs \<Longrightarrow> \<exists> ys zs. xs = ys @ x # zs \<and> x \<notin> elems ys"
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
    hence "x \<in> elems xs" using Cons.prems by auto
    thus ?thesis by (metis Cons.IH False UnE append_Cons elems.simps(2) empty_iff insert_iff)
  qed
qed

end
