import Mathlib.Data.Real.Basic

noncomputable
def T_L (x : ℝ) : ℝ := x/3

noncomputable
def T_R (x : ℝ) : ℝ := (2+x)/3

def pre_Cantor_set : ℕ → Set ℝ
  | 0 => Set.Icc 0 1
  | Nat.succ n => T_L '' pre_Cantor_set n ∪ T_R '' pre_Cantor_set n

def Cantor_set := iInf pre_Cantor_set


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
