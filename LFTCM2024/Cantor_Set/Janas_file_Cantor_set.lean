import Mathlib.Data.Real.Basic
import LFTCM2024.Cantor_Set.Cantor_Set
import Mathlib.Topology.Basic


noncomputable
def T_L (x : ℝ) : ℝ := x/3

noncomputable
def T_R (x : ℝ) : ℝ := (2+x)/3

def pre_Cantor_set : ℕ → Set ℝ
  | 0 => Set.Icc 0 1
  | Nat.succ n => T_L '' pre_Cantor_set (n) ∪ T_R '' pre_Cantor_set (n)

def Cantor_set := iInf pre_Cantor_set

lemma zero_in_Icc : (0 : ℝ) ∈ Set.Icc 0 1 := by
simp only [Set.mem_Icc]
simp only [le_refl]
simp only  [zero_le_one]
simp only [and_self]

lemma zero_in_pre_Cantor_set_0 : (0 : ℝ) ∈ pre_Cantor_set 0:= by
unfold pre_Cantor_set
apply zero_in_Icc

lemma Induction_step (n : ℕ): (0 : ℝ) ∈ pre_Cantor_set (n) → (0 : ℝ) ∈ pre_Cantor_set (n+1):= by
intro h
unfold pre_Cantor_set
simp only [Nat.add_eq, add_zero, Set.mem_union, Set.mem_image]
left
use 0
constructor
· exact h
· unfold T_L
  rw [@zero_div]



lemma zero_in_pre_Cantor_set (n : ℕ ) : (0 : ℝ) ∈ pre_Cantor_set n:= by
induction n with
  | zero => apply zero_in_pre_Cantor_set_0
  | succ n h =>
    apply Induction_step (n)
    exact h

lemma zero_in_Cantor : 0 ∈ Cantor_set := by
unfold Cantor_set
simp only [Set.iInf_eq_iInter, Set.mem_iInter]
apply zero_in_pre_Cantor_set


/-- instance Cantor_set.metricSpace : MetricSpace Cantor_set :=
  Subtype.metricSpace --/

#check Set.Icc 0 1
lemma Cantor_is_compact : IsCompact(Set.Icc 0 1)
