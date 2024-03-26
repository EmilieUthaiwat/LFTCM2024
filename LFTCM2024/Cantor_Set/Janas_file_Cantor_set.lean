import Mathlib.Data.Real.Basic

noncomputable
def T_L (x : ℝ) : ℝ := x/3

noncomputable
def T_R (x : ℝ) : ℝ := (2+x)/3

def pre_Cantor_set : ℕ → Set ℝ
  | 0 => Set.Icc 0 1
  | Nat.succ n => T_L '' pre_Cantor_set (n - 1) ∪ T_R '' pre_Cantor_set (n - 1)

def Cantor_set := iInf pre_Cantor_set


lemma zero_in_Cantor : 0 ∈ Cantor_set := by
unfold Cantor_set
simp only [Set.iInf_eq_iInter, Set.mem_iInter]
intro n
cases n
· unfold pre_Cantor_set
  simp only [Set.mem_Icc, le_refl, zero_le_one, and_self]
·sorry
