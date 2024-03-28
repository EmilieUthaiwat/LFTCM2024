import LFTCM2024.Cantor_Set.Cantor_Set

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

lemma third_Cantor_set_Union {n : ℕ} (hn : 1 ≤ n) :
T_L '' (pre_Cantor_set_Icc n) = pre_Cantor_set_Icc (n+1) ∩ Set.Icc 0 (1/3) := by
sorry


lemma twothirds_Cantor_set_Union {n : ℕ} (hn : 1 ≤ n) :
T_R '' (pre_Cantor_set_Icc n) =pre_Cantor_set_Icc (n+1) ∩ Set.Icc (2/3) 1 := by
sorry

lemma Cantor_set_Union_TL_TR {n : ℕ} (hn : 1 ≤ n):
T_L '' (pre_Cantor_set_Icc n) ∪ T_R '' (pre_Cantor_set_Icc n) =
pre_Cantor_set_Icc (n+1) ∩ pre_Cantor_set_Icc 1 := by
rw [third_Cantor_set_Union hn, twothirds_Cantor_set_Union hn, ← Set.inter_union_distrib_left]
simp only [pre_Cantor_set_Icc, pre_pre_Cantor_set_Icc, ge_iff_le, le_refl, tsub_eq_zero_of_le,
  pow_zero, nonpos_iff_eq_zero, pow_one,
  Set.iUnion_iUnion_eq_left, Nat.cast_zero, mul_zero, zero_div, zero_add, one_div, ne_eq,
  OfNat.ofNat_ne_zero, not_false_eq_true, div_self]


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


-- /- Function which takes n and k as input and gives the union of two closed intervals as output-/
-- def Cantor_set_union_Icc (n k : ℕ) : Set ℝ :=
--   Set.Icc ((3*k)/3^n) ((3*k+1)/3^n) ∪ Set.Icc ((3*k+2)/3^n) ((3*k+3)/3^n)

-- def f (n : ℕ) (k : ℕ) (_ : k ≤ 3^(n-1)-1) : Set ℝ :=
--   Cantor_set_union_Icc n k

-- def Cantor_set_Union_Icc (n : ℕ) := ⋃ (k : ℕ) (hk : k ≤ 3^(n-1)-1), f n k hk

-- /- The function g takes entries from [1,∞) -/
-- def g (i : ℕ) (_ : 1 ≤ i) : Set ℝ := Cantor_set_Union_Icc i

-- def Cantor_set_Icc := ⋂ (i : ℕ) (hi : 1 ≤ i), g i hi

-- def h (n : ℕ) (i : ℕ) (_ : i ≤ n) : Set ℝ := Cantor_set_Union_Icc i

-- def C'' (n : ℕ) : Set ℝ := ⋂ (i : ℕ) (hi : i ≤ n), h n i hi

-- theorem Cantor_set_Union_Icc_subset_C'' (n : ℕ) : C'' n ⊆ Cantor_set_Union_Icc n := by
--   refine' Set.iInter₂_subset n _
--   trivial

-- theorem Cantor_set_Union_Icc_eq_pre_Cantor_set (n : ℕ) (hn : 1 ≤ n) :
--     Cantor_set_Union_Icc n = pre_Cantor_set n := by
--   sorry

-- theorem Cantor_set_eq_Icc : Cantor_set = Cantor_set_Icc := by
--   sorry
