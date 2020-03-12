theory E3_1
  imports Main
begin

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun set :: "'a tree \<Rightarrow> 'a set" where
  "set Tip = {}" |
  "set (Node l v r) = (set l) \<union> {v} \<union> (set r)"

fun ord :: "int tree \<Rightarrow> bool" where
  "ord Tip = True" |
  "ord (Node Tip v Tip) = True" |
  "ord (Node (Node ll lv lr) v Tip) = ((lv < v) \<and> (ord (Node ll lv lr)))" |
  "ord (Node Tip v (Node rl rv rr)) = ((v < rv) \<and> (ord (Node rl rv rr)))" |
  "ord (Node (Node ll lv lr) v (Node rl rv rr)) = ((lv < v) \<and> (v < rv) \<and> (ord (Node ll lv lr)) \<and> (ord (Node rl rv rr)))"

fun ins :: "int tree \<Rightarrow> int \<Rightarrow> int tree" where
  "ins Tip x = Node Tip x Tip" |
  "ins (Node l v r) x = (if x = v then (Node l v r) else (if v < x then (Node l v (ins r x)) else (Node (ins l x) v r)))"

lemma "set (ins t x) = {x} \<union> set t"
  apply(induction t)
  apply(auto)
  done

lemma "ord t \<Longrightarrow> ord (ins t i)"
  apply(induction t rule: ord.induct)
  apply(auto)
  done

end
