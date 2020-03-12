theory E4_7
  imports Main
begin

datatype alpha = a | b

inductive S :: "alpha list \<Rightarrow> bool" where
S0 : "S []" |
S1 : "S w \<Longrightarrow> S (a # w @ [b])" |
S2 : "S w \<Longrightarrow> S v \<Longrightarrow> S (w @ v)"

fun balanced :: "nat \<Rightarrow> alpha list \<Rightarrow> bool" where
  "balanced 0 [] = True" |
  "balanced n (a # w) = balanced (n + 1) w" |
  "balanced n (b # w) = balanced (n - 1) w" |
  "balanced _ _ = False"

end
