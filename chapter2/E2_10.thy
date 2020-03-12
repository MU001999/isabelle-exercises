theory E2_10
  imports Main
begin

datatype tree0 = Leaf | Node tree0 tree0

fun nodes :: "tree0 ⇒ nat" where
  "nodes Leaf = 1" |
  "nodes (Node l r) = 1 + (nodes l) + (nodes r)"

fun explode :: "nat ⇒ tree0 ⇒ tree0" where
  "explode 0 t = t" |
  "explode (Suc n) t = explode n (Node t t)"

lemma "nodes (explode n t) = (nodes t) * (2 ^ n) + 2 ^ n - 1"
  apply(induction n arbitrary: t)
  apply(simp_all add: algebra_simps)
  done

end
