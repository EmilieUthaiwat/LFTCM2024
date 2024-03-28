import Mathlib.Data.Real.Basic
import Mathlib.Order.SetNotation
import Mathlib.Tactic.Linarith
import LFTCM2024.Cantor_Set.Cantor_Set
import LFTCM2024.Cantor_Set.Cantor_Team_3
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Perfect
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base

-- trying to formalize lemma 2.7 from here https://leanprover.zulipchat.com/user_uploads/3121/bDSQke-EKBZS9X4jpKYfs8Tq/report5.pdf
-- it is the ordered version of the general Brouwer theorem, see here for details https://arxiv.org/pdf/1210.1008.pdf
-- the lemma 2.7 is needed to prove the general statement, so this is not at all a waste of time
-- lemma 2.7 is enough to show that the Z_p are homeomorphic to eachother
-- Lemma 2.7 : Any compact perfect totally disconnected subset E of the real line is homeomorphic to the Cantor set C


open TopologicalSpace
-- we don't need to precise that it is metrizable since it is already a subset of ℝ
theorem Brouwer_ordered (E : Set ℝ) {hP : Preperfect E} {hT : TotallyDisconnectedSpace E} {hC : IsCompact E} :E ≃ Cantor_set := by
  set m:= Inf E
  set M:= Sup E
  sorry
