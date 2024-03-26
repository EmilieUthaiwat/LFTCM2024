import LFTCM2024.Cantor_Set.Cantor_Set

lemma cantor_sym (x : ℝ) (h: x ∈ Cantor_set): ((1-x) ∈ Cantor_set) := by
  sorry

lemma one_three_forth : (1/4 ∈ Cantor_set) := by
  unfold Cantor_set
  simp
  intro i
  induction i with
  | zero =>
  | succ n ih => sorry =>
