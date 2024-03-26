import LFTCM2024.Cantor_Set.Cantor_Set
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Perfect
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

instance Cantor_set.metricSpace : MetricSpace Cantor_set :=
  Subtype.metricSpace

lemma Cantor_set_closed : IsClosed Cantor_set  := by
  have : ∀ n, IsClosed (pre_Cantor_set n) := by
    intro n
    induction n with
    | zero =>
      simp[pre_Cantor_set]
      exact isClosed_Icc
    | succ n ih =>
      simp[pre_Cantor_set]
      refine IsClosed.union ?_ ?_
      · refine (ClosedEmbedding.closed_iff_image_closed ?succ.refine_1.hf).mp ih
        sorry
      ·
        sorry
  --refine { isOpen_compl := ?isOpen_compl }
  sorry


lemma Cantor_set_compact : IsCompact Cantor_set := by
  have : Cantor_set ⊆ Set.Icc 0 1 := by
    unfold Cantor_set
    sorry
  apply IsCompact.of_isClosed_subset _ Cantor_set_closed this
  exact isCompact_Icc


--the following two lemmas can be ignored

lemma Cantor_set_T2 : T2Space Cantor_set := by
  --exact instT2SpaceSubtypeInstTopologicalSpaceSubtype
  infer_instance
lemma Cantor_set_metrizable : TopologicalSpace.MetrizableSpace Cantor_set:= by
  infer_instance



lemma Cantor_set_preperfect : Preperfect Cantor_set := by --no isolated points
  sorry

lemma Cantor_set_tot_disc : TotallyDisconnectedSpace Cantor_set := by
  sorry
