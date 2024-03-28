import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Perfect
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base

noncomputable
def T_L (x : ℝ) : ℝ := x/3

noncomputable
def T_R (x : ℝ) : ℝ := (2+x)/3

def pre_Cantor_set : ℕ → Set ℝ
  | 0 => Set.Icc 0 1
  | Nat.succ n => T_L '' pre_Cantor_set n ∪ T_R '' pre_Cantor_set n

def Cantor_set := iInf pre_Cantor_set



/--
         First steps towards an equivalence with an alternative definition
         -----------------------------------------------------------------
--/

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


/--
         Simple exercises
         ----------------
--/


lemma quarters_everywhere : ∀ n : ℕ, 1/4 ∈ pre_Cantor_set n ∧ 3/4 ∈ pre_Cantor_set n := by
  intro n
  induction n with
  | zero =>
    unfold pre_Cantor_set
    simp only [one_div, Set.mem_Icc, inv_nonneg, Nat.ofNat_nonneg, true_and]
    apply And.intro
    · -- 1/4 is in pre_Cantor_set 0
      rw [inv_le_one_iff]
      norm_num

    . -- 3/4 is in pre_Cantor_set 0
      exact ⟨ by linarith, by linarith ⟩

  | succ n ih =>
    unfold pre_Cantor_set
    apply And.intro
    · -- goal: 1 / 4 ∈ pre_Cantor_set n
      rw [Set.mem_union]
      left
      rw [Set.mem_image]
      exists 3/4
      exact ⟨ ih.2, by unfold T_L; linarith ⟩

    · -- goal: 3 / 4 ∈ pre_Cantor_set n
      rw [Set.mem_union]
      right
      rw [Set.mem_image]
      exact ⟨1/4, ih.1, by unfold T_R; linarith ⟩

lemma one_quarters_everywhere : ∀ n : ℕ, 1/4 ∈ pre_Cantor_set n := by
  intro n
  exact (quarters_everywhere n).1

theorem one_quarters_is_in : 1/4 ∈ Cantor_set := by
  unfold Cantor_set
  unfold iInf

  simp only [Set.sInf_eq_sInter, Set.sInter_range, Set.mem_iInter]
  exact one_quarters_everywhere


lemma zero_is_everywhere : ∀ n : ℕ, 0 ∈ pre_Cantor_set n := by
  intro n
  induction n with
  | zero =>
    unfold pre_Cantor_set
    simp
  | succ n ih =>
    unfold pre_Cantor_set
    rw [Set.mem_union]
    left   -- we prove: 0 ∈ T_L '' pre_Cantor_set n
    rw [Set.mem_image]

    --  goal: ∃ x, x ∈ pre_Cantor_set n ∧ T_L x = 0
    exact ⟨0, ih, by unfold T_L; simp ⟩

theorem zero_is_in : 0 ∈ Cantor_set := by
  unfold Cantor_set
  unfold iInf

  simp only [Set.sInf_eq_sInter, Set.sInter_range, Set.mem_iInter]
  exact zero_is_everywhere


/--
         Standard topological facts
         --------------------------
--/


noncomputable def Homeomorph_T_L : Homeomorph ℝ ℝ where
  toFun := T_L
  invFun := fun x ↦ 3*x
  left_inv := by
    intro x
    unfold T_L
    simp only
    ring
  right_inv := by
    intro x
    unfold T_L
    simp only
    ring
  continuous_toFun := by
    unfold T_L
    simp only
    continuity
  continuous_invFun := by
    continuity

noncomputable def Homeomorph_T_R : Homeomorph ℝ ℝ where
  toFun := T_R
  invFun := fun x ↦ 3*x - 2
  left_inv := by
    intro x
    unfold T_R
    simp only
    ring
  right_inv := by
    intro x
    unfold T_R
    simp only
    ring
  continuous_toFun := by
    unfold T_R
    simp only
    continuity
  continuous_invFun := by
    continuity

instance Cantor_set.metricSpace : MetricSpace Cantor_set :=
  Subtype.metricSpace

lemma Cantor_set_closed : IsClosed Cantor_set  := by
  have h : ∀ n, IsClosed (pre_Cantor_set n) := by
    intro n
    induction n with
    | zero =>
      exact isClosed_Icc
    | succ n ih =>
      refine IsClosed.union ?_ ?_
      · refine (ClosedEmbedding.closed_iff_image_closed ?succ.refine_1.hf).mp ih
        apply Homeomorph.closedEmbedding Homeomorph_T_L
      · refine (ClosedEmbedding.closed_iff_image_closed ?succ.refine_2.hf).mp ih
        apply Homeomorph.closedEmbedding Homeomorph_T_R
  apply isClosed_iInter
  exact h

lemma Cantor_set_compact : IsCompact Cantor_set := by
  have : Cantor_set ⊆ Set.Icc 0 1 := by
    unfold Cantor_set
    intro x hx
    simp only [Set.iInf_eq_iInter, Set.mem_iInter] at hx
    exact hx 0
  apply IsCompact.of_isClosed_subset _ Cantor_set_closed this
  exact isCompact_Icc

lemma Cantor_set_T2 : T2Space Cantor_set := by
  infer_instance
lemma Cantor_set_metrizable : TopologicalSpace.MetrizableSpace Cantor_set := by
  infer_instance
