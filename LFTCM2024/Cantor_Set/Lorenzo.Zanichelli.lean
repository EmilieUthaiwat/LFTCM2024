import LFTCM2024.Cantor_Set.Cantor_Team_3
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Perfect


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
