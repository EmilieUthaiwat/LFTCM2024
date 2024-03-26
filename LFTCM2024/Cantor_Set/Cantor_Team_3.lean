import LFTCM2024.Cantor_Set.Cantor_Set
import Mathlib.Topology.MetricSpace.Basic

instance Cantor_set.metricSpace : MetricSpace Cantor_set :=
  Subtype.metricSpace
