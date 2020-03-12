theory E2_8
  imports Main
begin

fun intersperse :: "'a ⇒ 'a list ⇒ 'a list" where
  "intersperse a [] = []" |
  "intersperse a [x] = [x]" |
  "intersperse a (x # xs) = (x # [a]) @ (intersperse a xs)"

value "intersperse (1::nat) [2, 3, 4]"

lemma "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  apply(induction xs rule: intersperse.induct)
  apply(auto)
  done

end
