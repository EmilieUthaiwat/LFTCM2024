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



/- Function which takes n and k as input and gives the union of two closed intervals as output-/
def pre_pre_Cantor_set_Icc (n k : ℕ) : Set ℝ :=
  Set.Icc ((3*k)/3^n) ((3*k+1)/3^n) ∪ Set.Icc ((3*k+2)/3^n) ((3*k+3)/3^n)

-- def f (n : ℕ) (k : ℕ) (_ : k ≤ 3^(n-1)-1) : Set ℝ :=
  -- pre_pre_Cantor_set_Icc n k

-- def pre_Cantor_set_Icc (n : ℕ) := ⋃ (k : ℕ) (hk : k ≤ 3^(n-1)-1), f n k hk

def pre_Cantor_set_Icc (n : ℕ) := ⋃ (k : ℕ) (_ : k ≤ 3^(n-1)-1), pre_pre_Cantor_set_Icc n k


/- The function g takes entries from [1,∞) -/
-- def g (i : ℕ) (_ : 1 ≤ i) : Set ℝ := pre_Cantor_set_Icc i

-- def Cantor_set_Icc := ⋂ (i : ℕ) (hi : 1 ≤ i), g i hi

def Cantor_set_Icc := ⋂ (i : ℕ) (_ : 1 ≤ i), pre_Cantor_set_Icc i


def h (n : ℕ) (i : ℕ) (_ : i ≤ n) : Set ℝ := pre_Cantor_set_Icc i

/-
C'' n is the intersection of Cantor_set_Union_Icc l for l ≤ n
-/
def C'' (n : ℕ) : Set ℝ := ⋂ (i : ℕ) (hi : i ≤ n), h n i hi

theorem C''_subset_Cantor_set_Union_Icc
 (n : ℕ) : C'' n ⊆ pre_Cantor_set_Icc n := by
  refine' Set.iInter₂_subset n _
  trivial

lemma third_Cantor_set_Union (n : ℕ) :
T_L '' (pre_Cantor_set_Icc (n)) = pre_Cantor_set_Icc (n+1) ∩ Set.Icc (0) (1/3) := by
sorry

lemma twothirds_Cantor_set_Union (n : ℕ) :
T_R '' (pre_Cantor_set_Icc (n)) =pre_Cantor_set_Icc (n+1) ∩ Set.Icc (2/3) (1) := by
sorry

lemma Cantor_set_Union_TL_TR (n : ℕ) :
T_L '' (pre_Cantor_set_Icc (n)) ∪ T_R '' (pre_Cantor_set_Icc (n)) = pre_Cantor_set_Icc (n+1) ∩ pre_Cantor_set_Icc (1) := by
sorry

theorem inter_Cantor_set_Union_Icc_eq_pre_Cantor_set (n : ℕ) :
  pre_Cantor_set (n+1) = ⋂ (i : ℕ) (hi : i ≤ n), pre_Cantor_set_Icc (i+1) := by
  sorry
  -- The proof follows these steps:
  -- We use induction on n. pre_Cantor_set 1 = Cantor_set_Union_Icc 1 by unfolding (I guess)
  -- So assume pre_Cantor_set n = ⋂ Cantor_set_Union_Icc i, for 1≤ i ≤ n
  -- By definition, pre_Cantor_set (n+1) = T_L '' (pre_Cantor_set n) ∪ T_R '' (pre_Cantor_set n)
  -- By induction, pre_Cantor_set (n+1) = T_L '' (⋂ Cantor_set_Union_Icc i) ∪ T_R '' (⋂ Cantor_set_Union_Icc i)
  -- Since T_L and T_R are nice maps, we can move them inside the intersections to get:
  --  pre_Cantor_set (n+1) = ⋂ (T_L '' (Cantor_set_Union_Icc i) ∪ T_R '' (Cantor_set_Union_Icc i))
  --  by Cantor_set_Union_TL_TR, we have pre_Cantor_set (n+1) = ∩ (Cantor_set_Union_Icc (i+1) ∩ Cantor_set_Union_Icc (1))
  --  Now the right hand side is equal to ⋂ Cantor_set_Union_Icc (i+1) and we are done.

theorem Cantor_set_eq_Icc : Cantor_set = Cantor_set_Icc := by
  sorry
-- This proof is by using the fact that Cantor_set_Icc = ⋂ (n : ℕ) Cantor_set_union_Icc n
-- We have ⋂ (n : ℕ) Cantor_set_union_Icc n = Cantor_set_union_Icc 0 ∩ ⋂ (n : ℕ) Cantor_set_union_Icc (n+1)
