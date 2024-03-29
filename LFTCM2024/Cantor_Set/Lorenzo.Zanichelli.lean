import LFTCM2024.Cantor_Set.Cantor_Set

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
  -- · let z : ℝ := ((Nat.floor (x*3^n))/3^n:ℝ)  --(Nat.ceil (x*3^n)-(1) : ℕ)/3^n
  --   have : z∈ U∩ Cantor_set := by
  --     constructor
  --     · apply hball
  --       simp
  --       sorry --calculation...
  --     · apply (extremuses_of_Cantor_set ⟨x, hx⟩ n).1

  --   have : z≠ x := by
  --     push_neg at hy
  --     rw[hy.symm]
  --     sorry
  --   use z
