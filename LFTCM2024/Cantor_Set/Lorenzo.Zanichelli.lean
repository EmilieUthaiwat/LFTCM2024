import LFTCM2024.Cantor_Set.Cantor_Team_3
import Mathlib.Analysis.SpecialFunctions.Log.Base

-- --lemma Cantor_set_preperfect : Preperfect Cantor_set := by --no isolated points
--   intro x
--   intro hx
--   let ε : ℝ
--     let n : ℕ, n>
--   by
--     done
lemma extremuses_of_Cantor_set (n:ℕ) (k:ℕ) (h : k≤ 3^n) :
  (((k : ℝ)/(3^n)) ∈ Cantor_set) := by

  sorry

lemma LZCantor_set_preperfect : Preperfect Cantor_set := by
  rw [preperfect_iff_nhds]

  intro x hx U hU
  rw [ Metric.mem_nhds_iff] at hU
  obtain ⟨ ε , epos, hball ⟩ := hU
  let n : ℕ  := (Nat.ceil (Real.logb 3 (1/ε)))+1
  let y : ℝ := (Nat.ceil (x*3^n))/3^n
  by_cases hy : y≠ x
  · have : y∈ U∩ Cantor_set := by
      constructor
      · apply hball
        simp
        sorry
      · apply extremuses_of_Cantor_set
        simp
        sorry
    use y
  · let z : ℝ := (Nat.ceil (x*3^n)-(1) : ℕ)/3^n
    have : z∈ U∩ Cantor_set := by
      constructor
      · apply hball
        simp
        sorry
      · apply extremuses_of_Cantor_set
        simp
        sorry
    have : z≠ x :=
      sorry
    use z
