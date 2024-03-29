import Mathlib.Tactic
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Analysis.SpecialFunctions.Log.Base

noncomputable
def T_L (x : ℝ) : ℝ := x/3

noncomputable
def T_R (x : ℝ) : ℝ := (2+x)/3

def pre_Cantor_set : ℕ → Set ℝ
  | 0 => Set.Icc 0 1
  | Nat.succ n => T_L '' pre_Cantor_set n ∪ T_R '' pre_Cantor_set n

def Cantor_set := iInf pre_Cantor_set



/-
         First steps towards an equivalence with an alternative definition
         -----------------------------------------------------------------
-/

/- Function which takes n and k as input and gives the union of two closed intervals as output-/
-- def pre_pre_Cantor_set_Icc (n k : ℕ) : Set ℝ :=
  -- Set.Icc ((3*k)/3^n) ((3*k+1)/3^n) ∪ Set.Icc ((3*k+2)/3^n) ((3*k+3)/3^n)

-- def f (n : ℕ) (k : ℕ) (_ : k ≤ 3^(n-1)-1) : Set ℝ :=
  -- pre_pre_Cantor_set_Icc n k

-- def pre_Cantor_set_Icc (n : ℕ) := ⋃ (k : ℕ) (hk : k ≤ 3^(n-1)-1), f n k hk

/- Guys, please don't add the second definition here. It is giving errors in the team 1 file as we have to import this one anyway-/

def pre_pre_Cantor_set_Icc (n k : ℕ) : Set ℝ :=
  Set.Icc ((3*k)/3^n) ((3*k+1)/3^n) ∪ Set.Icc ((3*k+2)/3^n) ((3*k+3)/3^n)


def pre_Cantor_set_Icc (n : ℕ) := ⋃ (k : ℕ) (_ : k ≤ 3^(n-1)-1), pre_pre_Cantor_set_Icc n k


def Cantor_set_Icc := ⋂ (i : ℕ), pre_Cantor_set_Icc i

-- def h (n : ℕ) (i : ℕ) (_ : i ≤ n) : Set ℝ := pre_Cantor_set_Icc i

/-
C'' n is the intersection of Cantor_set_Union_Icc l for l ≤ n
-/
-- def C'' (n : ℕ) : Set ℝ := ⋂ (i : ℕ) (hi : i ≤ n), h n i hi

-- theorem C''_subset_Cantor_set_Union_Icc
--  (n : ℕ) : C'' n ⊆ pre_Cantor_set_Icc n := by
--   refine' Set.iInter₂_subset n _
--   trivial


/--
         Simple exercises
         ----------------
--/


lemma quarters_everywhere (n : ℕ) : 1/4 ∈ pre_Cantor_set n ∧ 3/4 ∈ pre_Cantor_set n := by
  induction n with
  | zero =>
    simp only [pre_Cantor_set, Set.mem_Icc, inv_nonneg, Nat.ofNat_nonneg, true_and]
    refine ⟨⟨?_, ?_ ⟩,?_,?_⟩ <;> linarith

  | succ n ih =>
    apply And.intro
    · -- goal: 1 / 4 ∈ pre_Cantor_set n
      exact Or.inl ⟨3/4, ih.2, by unfold T_L; linarith ⟩

    · -- goal: 3 / 4 ∈ pre_Cantor_set n
      exact Or.inr ⟨1/4, ih.1, by unfold T_R; linarith ⟩

lemma one_quarters_everywhere (n : ℕ) : 1/4 ∈ pre_Cantor_set n := (quarters_everywhere n).1

theorem one_quarters_is_in : 1/4 ∈ Cantor_set := by
  simp only [Cantor_set,iInf, Set.sInf_eq_sInter, Set.sInter_range, Set.mem_iInter]
  exact one_quarters_everywhere

lemma zero_is_everywhere : ∀ n : ℕ, 0 ∈ pre_Cantor_set n := by
  intro n
  induction n with
  | zero =>
    simp [pre_Cantor_set]
  | succ n ih =>
    --  goal: ∃ x, x ∈ pre_Cantor_set n ∧ T_L x = 0
    exact Or.inl ⟨0, ih, by unfold T_L; simp ⟩

theorem zero_is_in : 0 ∈ Cantor_set := by
  simp only [Cantor_set, iInf, Set.sInf_eq_sInter, Set.sInter_range, Set.mem_iInter]
  exact zero_is_everywhere


/--
         Standard topological facts
         --------------------------
--/

noncomputable def Homeomorph_T_L := Homeomorph.mulLeft₀ (1/3:ℝ) (by norm_num)

noncomputable def Homeomorph_T_R := (Homeomorph.addLeft (2:ℝ)).trans Homeomorph_T_L

lemma Cantor_set_subset_UnitInterval : Cantor_set ⊆ Set.Icc 0 1 := by
  intro x hx
  simp only [Cantor_set, Set.iInf_eq_iInter, Set.mem_iInter] at hx
  exact hx 0

instance Cantor_set.metricSpace : MetricSpace Cantor_set :=
  Subtype.metricSpace

lemma Cantor_set_closed : IsClosed Cantor_set  := by
  apply isClosed_iInter
  intro n
  induction n with
  | zero =>
    exact isClosed_Icc
  | succ n ih =>
    refine IsClosed.union ?_ ?_
    · refine (ClosedEmbedding.closed_iff_image_closed ?succ.refine_1.hf).mp ih
      convert Homeomorph_T_L.closedEmbedding
      ext x
      simp [T_L, Homeomorph_T_L, div_eq_inv_mul]
    · refine (ClosedEmbedding.closed_iff_image_closed ?succ.refine_2.hf).mp ih
      convert  Homeomorph_T_R.closedEmbedding
      ext x
      simp [T_R, Homeomorph_T_R, Homeomorph_T_L, div_eq_inv_mul]

lemma Cantor_set_compact : IsCompact Cantor_set :=
  isCompact_Icc.of_isClosed_subset Cantor_set_closed Cantor_set_subset_UnitInterval

lemma Cantor_set_T2 : T2Space Cantor_set := by
  infer_instance
lemma Cantor_set_metrizable : TopologicalSpace.MetrizableSpace Cantor_set := by
  infer_instance

--
--Proof of Cantor_set IsPerfect
--

lemma cipher (m n b : ℕ )(hb: b>1) (hm : n≤m) : ∀ x : ℝ, 0 ≤ x →  ((Nat.floor (x*(b^m)))/(b^m):ℝ)∈
Set.Icc (((Nat.floor (x*b^n):ℝ)/(b^n))) (((Nat.ceil (x*b^n): ℝ)/(b^n))) := by
simp
intro x hx
constructor
· have : (⌊x * ↑b ^ n⌋₊:ℝ) / b ^ n = (⌊x * ↑b ^ n⌋₊*b^(m-n)) / (b ^ n*b^(m-n)) := by
    rw [mul_div_mul_right]
    positivity
  rw[this, ← pow_add, Nat.add_sub_cancel' hm]
  gcongr
  norm_cast
  suffices ⌊x * ↑b ^ n⌋₊*b^(m-n)≤ x*b^m by
    rw[Nat.le_floor_iff]
    exact_mod_cast this
    positivity      --_ ≤ _ := sorry
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  simp only [add_comm n k, add_tsub_cancel_right, pow_add]
  rw [mul_comm ((b:ℝ)^k:ℝ), ← mul_assoc]
  gcongr
  apply Nat.floor_le
  positivity
· have : (⌈x * ↑b ^ n⌉₊:ℝ) / b ^ n = (⌈x * ↑b ^ n⌉₊*b^(m-n)) / (b ^ n*b^(m-n)) := by
    rw [mul_div_mul_right]
    positivity
  rw[this, ← pow_add, Nat.add_sub_cancel' hm]
  gcongr
  norm_cast
  apply le_trans (Nat.floor_le_ceil _)
  suffices ⌈x * ↑b ^ n⌉₊*b^(m-n)≥ x*b^m by
    rw[Nat.ceil_le]
    exact_mod_cast this
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  simp only [add_comm n k, add_tsub_cancel_right, pow_add]
  rw [mul_comm ((b:ℝ)^k:ℝ), ← mul_assoc]
  gcongr
  apply Nat.le_ceil

lemma foo (hx : x ∈  Cantor_set) (n m :ℕ) (hm: m<n):
(((Nat.floor (x*3^n):ℝ)/3^n))∈ Set.Icc (((Nat.floor (x*3^m):ℝ)/3^m)) (((Nat.ceil (x*3^m):ℝ)/3^m)) := by
apply cipher
· simp
· exact hm.le
· have : Cantor_set ⊆ Set.Icc 0 1 := by
    unfold Cantor_set
    intro x hx
    simp only [Set.iInf_eq_iInter, Set.mem_iInter] at hx
    exact hx 0
  suffices x∈ Set.Icc 0 1 by
    exact this.1
  exact this hx

lemma bar {n :ℕ}(m: ℕ)(hx : x ∈  Cantor_set) (hnice : ∀ a<n, x≠ (a:ℝ)/3^n) :
Set.Icc (((Nat.floor (x*3^m):ℝ)/3^m)) (((Nat.ceil (x*3^m):ℝ)/3^m))⊆ pre_Cantor_set_Icc m := by
sorry

lemma extremuses_of_Cantor_set_nice_x  (hx : x ∈  Cantor_set) (n :ℕ) (hnice : ∀ a<n, x≠ (a:ℝ)/3^n) :
(((Nat.floor (x*3^n))/3^n):ℝ)∈ Cantor_set := by--∧ (((Nat.ceil (x.1*3^n))/3^n):ℝ) ∈ Cantor_set :=
suffices h1:  ∀ m :ℕ,  ((((Nat.floor (x*3^n))/3^n):ℝ)∈ pre_Cantor_set_Icc m) by
  have : (⌊x * 3 ^ n⌋₊:ℝ) / 3 ^ n ∈ Cantor_set_Icc := by
    sorry --waiting for Cantor_set_Icc_mem............
  -- apply Cantor_set_eq_Icc
  sorry
intro m
by_cases hm : m ≥ n
· sorry
· push_neg at hm
  suffices (((Nat.floor (x*3^n))/3^n):ℝ)∈ Set.Icc (((Nat.floor (x*3^m))/3^m):ℝ) (((Nat.ceil (x*3^m))/3^m):ℝ) by
    apply bar m hx hnice
    exact this
  apply foo <;> assumption

#exit

lemma LZCantor_set_preperfect : Preperfect Cantor_set := by
rw [preperfect_iff_nhds]
intro x hx U hU
rw [ Metric.mem_nhds_iff] at hU
obtain ⟨ ε , epos, hball ⟩ := hU
let n : ℕ  := (Nat.ceil (Real.logb 3 (1/ε)))+1
have hnε : 3^(-(n:ℤ))<ε := by
        simp
        sorry  --calculations....
by_cases hnice : ∀ a<n, (x≠ (a:ℝ)/3^n)
· set y : ℝ := ((Nat.floor (x*3^n))/3^n:ℝ) with hy1
  --by_cases hy : y≠ x
  have : y∈ U∩ Cantor_set := by
    constructor
    · apply hball
      simp
      suffices x-y≤ (1/3^n) by
        sorry
      rw[hy1]
      rw[le_div_iff]
      sorry --calculations.......
      --rw[right_distrib]
      positivity
    · apply extremuses_of_Cantor_set_nice_x
      assumption
      assumption
  use y
  constructor
  · exact this
  · sorry
· push_neg at hnice
  sorry
