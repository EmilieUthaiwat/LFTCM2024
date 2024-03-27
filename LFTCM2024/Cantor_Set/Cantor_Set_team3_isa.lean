import LFTCM2024.Cantor_Set.Cantor_Team_3
-- import Mathlib.Topology.MetricSpace.Basic

-- instance Cantor_set.metricSpace : MetricSpace Cantor_set :=
--  Subtype.metricSpace

#check Cantor_set.metricSpace

lemma eq_of_dist_eq_zero_isa  : ∀ x :  Cantor_set,
∀ y : Cantor_set, Cantor_set.metricSpace.dist x  y = 0 → x = y := by
  apply MetricSpace.eq_of_dist_eq_zero

lemma Cantor_set_preperfect : Preperfect Cantor_set := by
  rw [preperfect_iff_nhds]

  intro x h U hU
  rw [ Metric.mem_nhds_iff] at hU
  obtain ⟨ ε , epos, hball ⟩ := hU
  unfold Metric.ball at hball
  let n := Nat.ceil (Real.logb 3 ε )
  have def2 : ∃ k : ℕ , (k ≤ 3^(n-1) -1) ∧
  ((x ∈ Set.uIcc (3*k/3^(n)) ((3*k+1)/3^n) ∨ (x ∈ Set.uIcc ((3*k+2)/(3^n)) ((3*k+3)/3^n) ))) := by sorry
 --no isolated points
  sorry
