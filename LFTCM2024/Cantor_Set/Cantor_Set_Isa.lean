import Mathlib.Data.Real.Basic

noncomputable
def T_L (x : ℝ) : ℝ := x/3

noncomputable
def T_R (x : ℝ) : ℝ := (2+x)/3

def pre_Cantor_set : ℕ → Set ℝ
  | 0 => Set.Icc 0 1
  | Nat.succ n => T_L '' pre_Cantor_set (n) ∪ T_R '' pre_Cantor_set (n)

def Cantor_set := iInf pre_Cantor_set

lemma inclus : ∀ n, pre_Cantor_set n ⊆  pre_Cantor_set (n-1) := by
 intro n
 apply [set.union_def]
 -- essai





lemma zero_in_C : 0 ∈ Cantor_set := by

  unfold Cantor_set
  unfold iInf

  simp only [Set.sInf_eq_sInter, Set.sInter_range, Set.mem_iInter]
  intro i
  induction i with (n;hn)
  rcases i with h1 | n
    --rw [Set.mem_def]
  --induction i
  · unfold pre_Cantor_set
    unfold Set.Icc
    refine Set.setOf_app_iff.mpr ?zero.a
    simp
  · unfold pre_Cantor_set
    simp
    --rw [@Set.union_def]

    --rw [@Set.image_eq_iUnion]
    --simp only [Set.mem_iUnion, Set.mem_singleton_iff, exists_prop, Set.mem_image]
    --unfold T_L
    --unfold T_R
    --rw [@Set.setOf_app_iff]
    constructor
    unfold T_L
    use 0
    constructor
    have  := inclus
    specialize this n

    ·induction

    · simp














  sorry

lemma one_third_in_C : 1/3 ∈  Cantor_set := by
  sorry

lemma one_fourth_in_C : 1/4 ∈  Cantor_set := by
  sorry
