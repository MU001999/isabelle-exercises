theory E2_2
  imports Main
begin

datatype nat = nil | suc nat

fun add :: "nat ⇒ nat ⇒ nat" where
  "add nil n = n" |
  "add (suc m) n = suc (add m n)"

lemma add_assoc : "add (add x y) z = add x (add y z)"
  apply(induction x)
  apply(auto)
  done

lemma add_02 [simp] : "add m nil = m"
  apply(induction m)
  apply(auto)
  done

lemma add_03 [simp] : "suc (add m n) = add m (suc n)"
  apply(induction m)
  apply(auto)
  done

lemma add_commut : "add m n = add n m"
  apply(induction m)
  apply(auto)
  done

fun double :: "nat⇒ nat" where
  "double nil = nil" |
  "double (suc m) = suc (suc (double m))"

lemma double_02 : "double m = add m m"
  apply(induction m)
  apply(auto)
  done

end
