theory E4_2
  imports Main
begin

lemma "∃ ys zs. xs = ys @ zs ∧ (length ys = length zs ∨ length ys = length zs + 1)"
proof cases
  let ?l1 = " take ((length xs div 2)) xs"
  let ?l2 = " drop ((length xs div 2)) xs"
  assume "even (length xs)"
  have "xs = ?l1 @ ?l2" by auto
  hence "length ?l1 = length ?l2" using ‹even (length xs)› by fastforce
  hence "xs = ?l1 @ ?l2 ∧ length ?l1 = length ?l2" by auto
  thus ?thesis by blast
next
  let ?l1 = " take ((length xs div 2) + 1) xs"
  let ?l2 = " drop ((length xs div 2) + 1) xs"
  assume "odd (length xs)"
  have "xs = ?l1 @ ?l2" by auto
  hence "length ?l1 = length ?l2 + 1" by (smt ‹odd (length xs)› add.commute add_diff_cancel_left' left_add_twice length_append length_drop odd_two_times_div_two_succ)
  hence "xs = ?l1 @ ?l2 ∧ length ?l1 = length ?l2 + 1" by auto
  thus ?thesis by blast
qed

end
