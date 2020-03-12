theory E2_11
  imports Main
begin

datatype exp = Var | Const int | Add exp exp | Mult exp exp

fun eval :: "exp ⇒ int ⇒ int" where
  "eval Var x = x" |
  "eval (Const e) x = e" |
  "eval (Add lhs rhs) x = (eval lhs x) + (eval rhs x)" |
  "eval (Mult lhs rhs) x = (eval lhs x) * (eval rhs x)"

fun evalp :: "int list ⇒ int ⇒ int" where
  "evalp [] v = 0" |
  "evalp (x # xs) v = x + v * (evalp xs v)"

fun add_coeffs :: "int list ⇒ int list ⇒ int list" where
  "add_coeffs [] rhs = rhs" |
  "add_coeffs lhs [] = lhs" |
  "add_coeffs (x # xs) (y # ys) = (x + y) # (add_coeffs xs ys)"

fun mul_coeffs :: "int list ⇒ int list ⇒ int list" where
  "mul_coeffs [] ys = []" |
  "mul_coeffs (x # xs) ys = add_coeffs (map ((*) x) ys) (0 # (mul_coeffs xs ys))"

fun coeffs :: "exp ⇒ int list" where
  "coeffs Var = [0, 1]" |
  "coeffs (Const c) = [c]" |
  "coeffs (Add lhs rhs) = add_coeffs (coeffs lhs) (coeffs rhs)" |
  "coeffs (Mult lhs rhs) = mul_coeffs (coeffs lhs) (coeffs rhs)"

lemma addcl [simp] : "evalp (add_coeffs A B) x = evalp A x + evalp B x"
  apply(induction A B rule: add_coeffs.induct)
  by (auto simp add: algebra_simps)

lemma mulcc [simp] : "evalp (map ((*) a) ys) x = a * evalp ys x"
  apply(induction ys)
  by (auto simp add: algebra_simps)

lemma mulcl [simp] : "evalp (mul_coeffs A B) x = evalp A x * evalp B x"
  apply(induction A arbitrary: B x)
  by (auto simp add: algebra_simps)

lemma "evalp (coeffs e) x = eval e x"
  apply(induction e rule: coeffs.induct)
  by (auto simp add: algebra_simps)

end
