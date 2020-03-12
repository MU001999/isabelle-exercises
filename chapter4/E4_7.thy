theory test
  imports Main
begin

datatype alpha = a | b

inductive S :: "alpha list ⇒ bool" where
S0 : "S []" |
S1 : "S w ⟹ S (a # w @ [b])" |
S2 : "S w ⟹ S v ⟹ S (w @ v)"

fun balanced :: "nat ⇒ alpha list ⇒ bool" where
  "balanced 0 [] = True" |
  "balanced n (a # w) = balanced (n + 1) w" |
  "balanced n (b # w) = balanced (n - 1) w" |
  "balanced _ _ = False"

end
