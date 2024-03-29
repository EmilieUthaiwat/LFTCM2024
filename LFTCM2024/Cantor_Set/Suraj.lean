import Mathlib.Data.Real.Basic
import Mathlib.Tactic

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


def pre_Cantor_set_Icc (n : ℕ) := ⋃ (k : ℕ) (_ : k ≤ 3^(n-1)-1), pre_pre_Cantor_set_Icc n k


def Cantor_set_Icc := ⋂ (i : ℕ), pre_Cantor_set_Icc i


lemma T_L_image_eq_inter {n : ℕ} (hn : 1 ≤ n) :
T_L '' (pre_Cantor_set_Icc n) = pre_Cantor_set_Icc (n+1) ∩ Set.Icc 0 (1/3) := by
sorry


lemma T_R_image_eq_inter {n : ℕ} (hn : 1 ≤ n) :
T_R '' (pre_Cantor_set_Icc n) =pre_Cantor_set_Icc (n+1) ∩ Set.Icc (2/3) 1 := by
sorry

lemma T_L_union_T_R_eq_inter {n : ℕ} (hn : 1 ≤ n):
T_L '' (pre_Cantor_set_Icc n) ∪ T_R '' (pre_Cantor_set_Icc n) =
pre_Cantor_set_Icc (n+1) ∩ pre_Cantor_set_Icc 1 := by
rw [T_L_image_eq_inter hn, T_R_image_eq_inter hn, ← Set.inter_union_distrib_left]
simp only [pre_Cantor_set_Icc, pre_pre_Cantor_set_Icc, ge_iff_le, le_refl, tsub_eq_zero_of_le,
  pow_zero, nonpos_iff_eq_zero, pow_one,
  Set.iUnion_iUnion_eq_left, Nat.cast_zero, mul_zero, zero_div, zero_add, one_div, ne_eq,
  OfNat.ofNat_ne_zero, not_false_eq_true, div_self]

theorem pre_Cantor_eq_Inter_pre_Cantor_Icc (n : ℕ) :
  pre_Cantor_set (n+1) = ⋂ (i : ℕ) (hi : i ≤ n), pre_Cantor_set_Icc (i+1) := by
  induction n with
  | zero =>
    simp only [Nat.zero_eq, zero_add, nonpos_iff_eq_zero, Set.iInter_iInter_eq_left]
    rw[pre_Cantor_set, pre_Cantor_set_Icc]
    simp only [ge_iff_le, le_refl, tsub_eq_zero_of_le, pow_zero, nonpos_iff_eq_zero,
      Set.iUnion_iUnion_eq_left]
    unfold pre_Cantor_set pre_pre_Cantor_set_Icc
    simp only [Nat.cast_zero, mul_zero, pow_one, zero_div, zero_add, one_div, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, div_self]
    have h1 :  T_L '' Set.Icc 0 1 = Set.Icc 0 (1/3) := by
      simp [T_L, div_eq_mul_inv]
      have := Set.image_mul_right_Icc
        (show 0 ≤ (1 : ℝ) by norm_num) (show 0 ≤ (3⁻¹ : ℝ) by norm_num)
      simpa using this
    have h2 :  T_R '' Set.Icc 0 1 = Set.Icc (2/3) 1 := by
      simp [T_R, div_eq_mul_inv]
      have key : (2 + · : ℝ → ℝ) '' (Set.Icc 0 1) = Set.Icc 2 3 := by
        simpa [show 2 + 1 = (3 : ℝ) by norm_num] using Set.image_const_add_Icc (2 : ℝ) 0 1
      have : (· * 3⁻¹ : ℝ → ℝ) '' Set.Icc 2 3 = Set.Icc (2 * 3⁻¹) 1 := by
        simpa using Set.image_mul_right_Icc
          (show 2 ≤ (3 : ℝ) by norm_num) (show 0 ≤ (3⁻¹ : ℝ) by norm_num)
      simp_rw [← this, ← key, ← Set.image_comp]
      rfl
    rw [h1, one_div, h2]
  | succ n ih =>
    unfold pre_Cantor_set
    dsimp
    have bij1 : Function.Bijective T_L := sorry
    have bij2 : Function.Bijective T_R := sorry
    -- simp_rw [ih, Set.image_iInter₂ bij1, Set.image_iInter₂ bij2, Set.union_iInter, Set.iInter_union,
      -- T_L_union_T_R_eq_inter (show (1 : ℕ) ≤ _ + 1 by norm_num)]

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
  unfold Cantor_set Cantor_set_Icc
  have h1 : ⋂ n, pre_Cantor_set_Icc n = ⋂ (n : ℕ) , pre_Cantor_set_Icc (n+1) ∩ pre_Cantor_set_Icc 0 := by
   sorry
  have h2 : ⋂ (n : ℕ) , pre_Cantor_set_Icc (n+1) =
    ⋂ (n : ℕ) , (⋂ (i : ℕ) (hi : i ≤ n), pre_Cantor_set_Icc (i+1)) := by sorry
  simp_rw [← pre_Cantor_eq_Inter_pre_Cantor_Icc] at h2
  rw [h1]
  have h3: ⋂ n, pre_Cantor_set_Icc (n + 1) ∩ pre_Cantor_set_Icc 0 =
    pre_Cantor_set_Icc 0 ∩ ⋂ n, pre_Cantor_set_Icc (n + 1) := by sorry
  rw [h3, h2]
  have h4: pre_Cantor_set_Icc 0 = pre_Cantor_set 0 ∪ Set.Icc 2 3 := by sorry
  have h5: (pre_Cantor_set 0 ∪ Set.Icc 2 3) ∩ ⋂ n, pre_Cantor_set (n + 1) =
    ⋂ n, pre_Cantor_set n := by sorry
  rw [h4, h5]
  simp
