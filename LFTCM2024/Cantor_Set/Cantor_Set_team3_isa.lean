import LFTCM2024.Cantor_Set.Cantor_Team_3
-- import Mathlib.Topology.MetricSpace.Basic

-- instance Cantor_set.metricSpace : MetricSpace Cantor_set :=
--  Subtype.metricSpace

#check Cantor_set.metricSpace

lemma eq_of_dist_eq_zero_isa  : ∀ x :  Cantor_set,
∀ y : Cantor_set, Cantor_set.metricSpace.dist x  y = 0 → x = y := by
  apply MetricSpace.eq_of_dist_eq_zero
