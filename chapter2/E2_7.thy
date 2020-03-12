theory E2_7
  imports Main
begin

datatype 'a tree = Leaf 'a | Node "'a tree" 'a "'a tree"

fun mirror :: "'a tree \<Rightarrow> 'a tree" where
  "mirror (Leaf v) = Leaf v" |
  "mirror (Node l v r) = Node (mirror r) v (mirror l)"

fun pre_order :: "'a tree \<Rightarrow> 'a list" where
  "pre_order (Leaf v) = [v]" |
  "pre_order (Node l v r) = v # (pre_order l) @ (pre_order r)"

fun post_order :: "'a tree \<Rightarrow> 'a list" where
  "post_order (Leaf v) = [v]" |
  "post_order (Node l v r) = (post_order l) @ (post_order r) @ [v]"

value "pre_order (mirror (Node (Leaf 1) (2::nat) (Node (Leaf 3) 4 (Node (Leaf 5) 6 (Leaf 7)))))"
value "rev (post_order (Node (Leaf 1) (2::nat) (Node (Leaf 3) 4 (Node (Leaf 5) 6 (Leaf 7)))))"

lemma "pre_order (mirror t) = rev (post_order t)"
  apply(induction t)
  apply(auto)
  done

(*
datatype 'a tree = Til | Node "'a tree" 'a "'a tree"

fun mirror :: "'a tree \<Rightarrow> 'a tree" where
  "mirror Til = Til" |
  "mirror (Node l v r) = Node (mirror r) v (mirror l)"

fun pre_order :: "'a tree \<Rightarrow> 'a list" where
  "pre_order Til = []" |
  "pre_order (Node l v r) = v # (pre_order l) @ (pre_order r)"

fun post_order :: "'a tree \<Rightarrow> 'a list" where
  "post_order Til = []" |
  "post_order (Node l v r) = (post_order l) @ (post_order r) @ [v]"

value "pre_order (mirror (Node Til (1::nat) (Node Til 2 (Node Til 3 Til))))"
value "rev (post_order (Node Til (1::nat) (Node Til 2 (Node Til 3 Til))))"

lemma "pre_order (mirror t) = rev (post_order t)"
  apply(induction t)
  apply(auto)
  done
*)

end
