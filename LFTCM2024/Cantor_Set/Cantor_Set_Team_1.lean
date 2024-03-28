import LFTCM2024.Cantor_Set.Cantor_Set

/- Function which takes n and k as input and gives the union of two closed intervals as output-/
def Cantor_set_union_Icc (n k : ℕ) : Set ℝ :=
  Set.Icc ((3*k)/3^n) ((3*k+1)/3^n) ∪ Set.Icc ((3*k+2)/3^n) ((3*k+3)/3^n)

def f (n : ℕ) (k : ℕ) (_ : k ≤ 3^(n-1)-1) : Set ℝ :=
  Cantor_set_union_Icc n k

def Cantor_set_Union_Icc (n : ℕ) := ⋃ (k : ℕ) (hk : k ≤ 3^(n-1)-1), f n k hk

/- The function g takes entries from [1,∞) -/
def g (i : ℕ) (_ : 1 ≤ i) : Set ℝ := Cantor_set_Union_Icc i

def Cantor_set_Icc := ⋂ (i : ℕ) (hi : 1 ≤ i), g i hi

def h (n : ℕ) (i : ℕ) (_ : i ≤ n) : Set ℝ := Cantor_set_Union_Icc i

def C'' (n : ℕ) : Set ℝ := ⋂ (i : ℕ) (hi : i ≤ n), h n i hi

theorem Cantor_set_Union_Icc_subset_C'' (n : ℕ) : C'' n ⊆ Cantor_set_Union_Icc n := by
  refine' Set.iInter₂_subset n _
  trivial

theorem Cantor_set_Union_Icc_eq_pre_Cantor_set (n : ℕ) (hn : 1 ≤ n) :
    Cantor_set_Union_Icc n = pre_Cantor_set n := by
  sorry

theorem Cantor_set_eq_Icc : Cantor_set = Cantor_set_Icc := by
  sorry
