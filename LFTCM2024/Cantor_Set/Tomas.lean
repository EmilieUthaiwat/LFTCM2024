import Mathlib.Data.Real.Basic
import Mathlib.Order.SetNotation
import LFTCM2024.Cantor_Set.Cantor_Set

-- def pre_Cantor_set : ℕ → Set ℝ
--   | 0 => Set.Icc 0 1
--   | Nat.succ n => T_L '' pre_Cantor_set (n - 1) ∪ T_R '' pre_Cantor_set (n - 1)
--
-- def Cantor_set := iInf pre_Cantor_set

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


/-
TODO

1) 1/4 in C
2) Compact, metrizable (T2), no isolated point, totally disconnected
3) any other such is C
4) Zp ~ Zq for any primes p,q
5) show that {0,1}^N is a Cantor set
-/
