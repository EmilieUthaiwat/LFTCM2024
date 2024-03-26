import LFTCM2024.Cantor_Set.Cantor_Team_3
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic

noncomputable def Homeomorph_T_L : Homeomorph ℝ ℝ where
  toFun := T_L
  invFun := fun x ↦ 3*x
  left_inv := by
    intro x
    unfold T_L
    simp only
    ring
  right_inv := by
    intro x
    unfold T_L
    simp only
    ring
  continuous_toFun := by
    unfold T_L
    simp only
    continuity
  continuous_invFun := by
    continuity

noncomputable def Homeomorph_T_R : Homeomorph ℝ ℝ where
  toFun := T_R
  invFun := fun x ↦ 3*x - 2
  left_inv := by
    intro x
    unfold T_R
    simp only
    ring
  right_inv := by
    intro x
    unfold T_R
    simp only
    ring
  continuous_toFun := by
    unfold T_R
    simp only
    continuity
  continuous_invFun := by
    continuity
