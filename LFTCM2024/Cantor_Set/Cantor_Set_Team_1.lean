import LFTCM2024.Cantor_Set.Cantor_Set

def Cantor_set_union_Icc (n k : ℕ) : Set ℝ :=
  Set.Icc ((3*k)/3^n) ((3*k+1)/3^n) ∪ Set.Icc ((3*k+2)/3^n) ((3*k+3)/3^n)

def f (n : ℕ) : Set.Icc 0 (3^(n-1)-1) → Set ℝ :=
  fun k => Cantor_set_union_Icc n k

def Cantor_set_Union_Icc (n : ℕ) := iSup (f n)

def g : Set.Ici 1 → Set ℝ := fun n => Cantor_set_Union_Icc n

def Cantor_set_Icc := iInf g

def h (n : ℕ) : Set.Icc 0 n → Set ℝ := fun l => Cantor_set_Union_Icc l

def C'' : ℕ → Set ℝ :=
  fun n => (Cantor_set_Union_Icc n ∩ Cantor_set_Union_Icc (n-1)) ∪ iInf (h n)

theorem Cantor_set_Union_Icc_subset : ∀ n, Cantor_set_Union_Icc n ⊆ Cantor_set_Union_Icc (n+1) := by
  sorry

theorem Cantor_set_Union_Icc_subset_C'' (n : ℕ) : C'' (n+1) ⊆ Cantor_set_Union_Icc (n+1) := by
  sorry

theorem Cantor_set_eq_Icc : Cantor_set = Cantor_set_Icc := by
  sorry
