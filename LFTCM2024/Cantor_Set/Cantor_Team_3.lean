import LFTCM2024.Cantor_Set.Cantor_Set
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Perfect
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base

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

instance Cantor_set.metricSpace : MetricSpace Cantor_set :=
  Subtype.metricSpace

lemma Cantor_set_closed : IsClosed Cantor_set  := by
  have h : ∀ n, IsClosed (pre_Cantor_set n) := by
    intro n
    induction n with
    | zero =>
      exact isClosed_Icc
    | succ n ih =>
      refine IsClosed.union ?_ ?_
      · refine (ClosedEmbedding.closed_iff_image_closed ?succ.refine_1.hf).mp ih
        apply Homeomorph.closedEmbedding Homeomorph_T_L
      · refine (ClosedEmbedding.closed_iff_image_closed ?succ.refine_2.hf).mp ih
        apply Homeomorph.closedEmbedding Homeomorph_T_R
  apply isClosed_iInter
  exact h


lemma Cantor_set_compact : IsCompact Cantor_set := by
  have : Cantor_set ⊆ Set.Icc 0 1 := by
    unfold Cantor_set
    intro x hx
    simp only [Set.iInf_eq_iInter, Set.mem_iInter] at hx
    exact hx 0
  apply IsCompact.of_isClosed_subset _ Cantor_set_closed this
  exact isCompact_Icc


--the following two lemmas can be ignored

lemma Cantor_set_T2 : T2Space Cantor_set := by
  --exact instT2SpaceSubtypeInstTopologicalSpaceSubtype
  infer_instance
lemma Cantor_set_metrizable : TopologicalSpace.MetrizableSpace Cantor_set:= by
  infer_instance


-- A Space is preperfect if it has no isolated points. Check the Mathlib docs for more info
lemma Cantor_set_preperfect : Preperfect Cantor_set := by
  rw [preperfect_iff_nhds]

  intro x h U hU
  rw [ Metric.mem_nhds_iff] at hU
  obtain ⟨ ε , epos, hball ⟩ := hU
  unfold Metric.ball at hball
  let n := Nat.ceil (Real.logb 3 ε )
  --have def2 : ∃ k : ℕ , (k ≤ 3^(n-1) -1) ∧
  --((x ∈ Set.uIcc (3*k/3^(n)) ((3*k+1)/3^n) ∨ (x ∈ Set.uIcc ((3*k+2)/(3^n)) ((3*k+3)/3^n) ))) := by sorry
 --no isolated points
  sorry

lemma Cantor_set_tot_disc : TotallyDisconnectedSpace Cantor_set := by
  apply (totallyDisconnectedSpace_iff Cantor_set).2
  intro S hS h₁S x h₁x y h₁y
  by_contra nhxy
  unfold IsPreconnected at h₁S
  have h : x < y ∨ x = y ∨ y < x := by
    exact lt_trichotomy x y
  rcases (lt_trichotomy x y) with xsmallery | ysmallerx
  · have hN : ∃ N : ℕ, N > 0 ∧ 1/ (3^N) < |(y:ℝ) - (x:ℝ)| := by sorry
    obtain ⟨z, hz⟩ : ∃ z : ℝ, z ∉ Cantor_set ∧ x < z ∧ z < y := by sorry
    -- use z= x + 1/2*3^N
    set A : Set Cantor_set := {x | (x: ℝ) ∈ Set.Ioo 0 z}
    set B : Set Cantor_set := {x | (x: ℝ) ∈ Set.Ioo z 1}
    have hfinal_1 : IsOpen A ∧ IsOpen B ∧ Cantor_set ⊆ A ∪ B ∧ Set.Nonempty (Cantor_set ∪ A) ∧
       Set.Nonempty (Cantor_set ∪ B) := by sorry
    have bla : ¬ Set.Nonempty (S ∩ (A ∩ B)) := by sorry
    apply bla
    apply h₁S
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
  · rcases ysmallerx with h1 | h2
    · apply nhxy
      assumption
    · sorry
