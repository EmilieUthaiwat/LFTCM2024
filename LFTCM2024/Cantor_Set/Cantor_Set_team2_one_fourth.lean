import Mathlib.Data.Real.Basic
import Mathlib.Order.SetNotation
import Mathlib.Tactic.Linarith
import LFTCM2024.Cantor_Set.Cantor_Set
import LFTCM2024.Cantor_Set.Cantor_Team_3

-- proofs of 0, 1/4 (and 3/4) are in the triadic Cantor

lemma quarters_everywhere' : ∀ n : ℕ, 1/4 ∈ pre_Cantor_set n ∧ 3/4 ∈ pre_Cantor_set n := by
  intro n
  induction n with
  | zero =>
    unfold pre_Cantor_set
    simp only [one_div, Set.mem_Icc, inv_nonneg, Nat.ofNat_nonneg, true_and]
    apply And.intro
    · -- 1/4 is in pre_Cantor_set 0
      rw [inv_le_one_iff]
      norm_num

    . -- 3/4 is in pre_Cantor_set 0
      rw [div_nonneg_iff]
      apply And.intro

      -- goal: 0 ≤ 3 ∧ 0 ≤ 4 ∨ 3 ≤ 0 ∧ 4 ≤ 0
      left
      simp

      -- goal: 3 / 4 ≤ 1
      rw [div_le_one_iff]
      left
      simp
      linarith

  | succ n ih =>
    unfold pre_Cantor_set
    apply And.intro
    · rw [Set.mem_union]
      left
      rw [Set.mem_image]
      exists 3/4

      apply And.intro
      · exact ih.2
      · unfold T_L
        linarith

    · rw [Set.mem_union]
      right
      rw [Set.mem_image]
      exists 1/4

      apply And.intro
      · exact ih.1
      · unfold T_R
        linarith

lemma one_quarters_everywhere : ∀ n : ℕ, 1/4 ∈ pre_Cantor_set n := by
  intro n
  exact (quarters_everywhere n).1

theorem quarters_is_in : 1/4 ∈ Cantor_set := by
  unfold Cantor_set
  unfold iInf

  simp only [Set.sInf_eq_sInter, Set.sInter_range, Set.mem_iInter]
  exact one_quarters_everywhere

lemma zero_is_everywhere : ∀ n : ℕ, 0 ∈ pre_Cantor_set n := by
  intro n
  induction n with
  | zero =>
    unfold pre_Cantor_set
    simp
  | succ n ih =>
    unfold pre_Cantor_set
    rw [Set.mem_union]
    left   -- we prove: 0 ∈ T_L '' pre_Cantor_set n
    rw [Set.mem_image]

    --  goal: ∃ x, x ∈ pre_Cantor_set n ∧ T_L x = 0
    use 0  -- we pick x=0

    apply And.intro
    · exact ih
    · unfold T_L
      simp

theorem zero_is_in : 0 ∈ Cantor_set := by
  unfold Cantor_set
  unfold iInf

  simp only [Set.sInf_eq_sInter, Set.sInter_range, Set.mem_iInter]
  exact zero_is_everywhere
