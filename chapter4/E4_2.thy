theory E4_2
  imports Main
begin

lemma "\<exists> ys zs. xs = ys @ zs \<and> (length ys = length zs \<or> length ys = length zs + 1)"
proof cases
  let ?l1 = "take ((length xs div 2)) xs"
  let ?l2 = "drop ((length xs div 2)) xs"
  assume "even (length xs)"
  hence "xs = ?l1 @ ?l2 \<and> length ?l1 = length ?l2" by auto
  thus ?thesis by blast
next
  let ?l1 = "take ((length xs div 2) + 1) xs"
  let ?l2 = "drop ((length xs div 2) + 1) xs"
  assume "odd (length xs)"
  hence "xs = ?l1 @ ?l2 \<and> length ?l1 = length ?l2 + 1" by (smt add.commute add_diff_cancel_right' append_take_drop_id left_add_twice length_append length_drop odd_two_times_div_two_succ)
  thus ?thesis by blast
qed

end
