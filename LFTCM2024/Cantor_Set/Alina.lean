import LFTCM2024.Cantor_Set.Cantor_Set
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

lemma zero_in_cantor : 0 ∈ Cantor_set := by
 unfold Cantor_set
 simp
 intro i
 induction i with
 | zero =>
   unfold pre_Cantor_set
   simp

 | succ n ih =>
   unfold pre_Cantor_set
   left
   simp
   use 0
   constructor
   assumption
   unfold T_L
   exact zero_div 3

lemma cantor_symm (x : ℝ) (h: x ∈ Cantor_set) : (1-x ∈ Cantor_set) := by
  sorry

lemma one_forth_in_cantor : (1/4 ∈ Cantor_set) := by
  unfold Cantor_set
  simp
  intro i
  induction i with
  | zero =>
    unfold pre_Cantor_set
    simp
    norm_num

  | succ n ih =>
    unfold pre_Cantor_set
    have (h : 3/4 ∈ Cantor_set) := by
      exact ih
      apply cantor_symm at 1/4
    sorry
