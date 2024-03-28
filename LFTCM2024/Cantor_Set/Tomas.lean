import Mathlib.Data.Real.Basic
import Mathlib.Order.SetNotation
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Log.Base
import LFTCM2024.Cantor_Set.Cantor_Set

-- def pre_Cantor_set : ℕ → Set ℝ
--   | 0 => Set.Icc 0 1
--   | Nat.succ n => T_L '' pre_Cantor_set n ∪ T_R '' pre_Cantor_set n
--
-- def Cantor_set := iInf pre_Cantor_set

lemma obvious_inclusion : Cantor_set ⊆ Set.Icc 0 1 := by
  intro x
  unfold Cantor_set
  intro h
  simp only [Set.iInf_eq_iInter, Set.mem_iInter] at h
  exact h 0

----------------------------

lemma map_to_product (x : ℝ) : (ℕ → Bool) := by
  intro n
  let p := T_L x ∈ pre_Cantor_set n

  let d : Decidable p := by
    by_cases c : p   -- use excluded middle on p
    · exact isTrue c
    · exact isFalse c
    -- note: tactic `classical` solves this goal but then exact below fails...
  exact decide p

lemma map_from_product_one (f : ℕ → Bool) (n : ℕ) : pre_Cantor_set n := by
  induction n with
  | zero =>
    unfold pre_Cantor_set
    use 1/2
    norm_num
  | succ n2 ih  =>
    let ⟨el, prf⟩ := ih
    if f n2
      then use T_L el
           unfold pre_Cantor_set
           rw [Set.mem_union]
           left
           simp only [Set.mem_image]
           use el
      else use T_R el
           unfold pre_Cantor_set
           rw [Set.mem_union]
           right
           simp only [Set.mem_image]
           use el


-- inspired by https://math.stackexchange.com/questions/253535/the-cantor-ternary-set-is-totally-disconnected
lemma Cantor_sep_index (x : ℝ) (y : ℝ) : ℕ  := by
  -- we know that no later than in n : ℕ, 3^(-n) < |x-y|
  -- then for this n we have that x and y appear in different copies of T_L/T_R image of pre_Cantor_set n
  let a := abs (x-y)
  let l := Real.logb 3 a
  exact Nat.ceil l

-- Maybe it would be better to compute the function iteratively
-- lemma Cantor_sep_index {x : ℝ} {y : ℝ} (hx : x ∈ Cantor_set) (hy : y ∈ Cantor_set) (hf : x < y) : ℕ 
  -- let s : Set ℕ := { n | 1/(3^n) < a }
  -- WANT stg like: exact max s


-- lemma separate_in_pre_Cantor (x : Cantor_set) (y : Cantor_set) (hf : x < y) : x ∈ T_L '' pre_Cantor_set (Cantor_sep_index x y hf) ∧ y ∈ T_R '' pre_Cantor_set (Cantor_sep_index x y hf) := by sorry


----------------------------

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
      apply And.intro
      linarith
      linarith

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
      exists 1/4
      exact ⟨ ih.1, by unfold T_R; linarith ⟩

lemma one_quarters_everywhere : ∀ n : ℕ, 1/4 ∈ pre_Cantor_set n := by
  intro n
  exact (quarters_everywhere n).1

theorem one_quarters_is_in : 1/4 ∈ Cantor_set := by
  unfold Cantor_set
  unfold iInf

  simp only [Set.sInf_eq_sInter, Set.sInter_range, Set.mem_iInter]
  exact one_quarters_everywhere

----------------------------

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
    use 0  -- we pick x=0

    apply And.intro
    · exact ih
    · unfold T_L
      simp

theorem zero_is_in : 0 ∈ Cantor_set := by
  unfold Cantor_set
  unfold iInf

  simp only [Set.sInf_eq_sInter, Set.sInter_range, Set.mem_iInter]
  exact zero_is_everywhere


----------------------------


/-
TODO

1) 1/4 in C
2) Compact, metrizable (T2), no isolated point, totally disconnected
3) any other such is C
4) Zp ~ Zq for any primes p,q
5) show that {0,1}^N is a Cantor set
-/
