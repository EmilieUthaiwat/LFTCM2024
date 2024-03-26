import LFTCM2024.Cantor_Set.Cantor_Set

def pre_pre_Cantor_set_explicit (n k : ℕ) : Set ℝ :=
  Set.Icc (3*k/3^n) (3*k+1/3^n) ∪ Set.Icc (3*k+2/3^n) (3*k+3/3^n)

def f (n : ℕ) : Set.Icc 0 (3^(n-1)-1) → Set ℝ :=
  fun k => pre_pre_Cantor_set_explicit n k

def pre_Cantor_set_explicit (n : ℕ) := iSup (f n)

def g : Set.Ici 1 → Set ℝ := fun n => pre_Cantor_set_explicit n

def Cantor_set_explicit := iInf g

theorem Cantor_set_eq_explicit : Cantor_set = Cantor_set_explicit := by
