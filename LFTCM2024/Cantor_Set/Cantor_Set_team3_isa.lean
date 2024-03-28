import LFTCM2024.Cantor_Set.Cantor_Team_3
import LFTCM2024.Cantor_Set.Cantor_Set_Team_1
-- import Mathlib.Topology.MetricSpace.Basic

-- instance Cantor_set.metricSpace : MetricSpace Cantor_set :=
--  Subtype.metricSpace


lemma foo (hx : x ∈  Cantor_set) (n :ℕ) (hnice : ∀ a<n, x≠ (a:ℝ)/3^n) :
∀m<n, (((Nat.floor (x*3^n))/3^n):ℝ)∈ Set.Icc (((Nat.floor (x*3^m))/3^m):ℝ) (((Nat.floor (x*3^m))/3^m):ℝ) := by
sorry

lemma extremuses_of_Cantor_set_nice_x  (hx : x ∈  Cantor_set) (n :ℕ) (hnice : ∀ a<n, x≠ (a:ℝ)/3^n) :
(((Nat.floor (x*3^n))/3^n):ℝ)∈ Cantor_set :=--∧ (((Nat.ceil (x.1*3^n))/3^n):ℝ) ∈ Cantor_set :=
by
suffices h1:  ∀ m :ℕ,  ((((Nat.floor (x*3^n))/3^n):ℝ)∈ pre_Cantor_set_Icc m) from by
  sorry
intro m
by_cases hm : m≥  n
· unfold pre_Cantor_set_Icc
  simp_rw [Cantor_set, pre_Cantor_set] at hx
  rw  [Set.mem_iUnion]
  set k := Nat.floor (x*3^(n+1)) with k_def
  simp_rw [Set.mem_iUnion]
  -- simp [pre_pre_Cantor_set_Icc​]

  use 3^(m-n)*k


  refine ⟨ ?_, ?_⟩
  refine hm



  sorry
· sorry
sorry







#check Cantor_set.metricSpace

lemma eq_of_dist_eq_zero_isa  : ∀ x :  Cantor_set,
∀ y : Cantor_set, Cantor_set.metricSpace.dist x  y = 0 → x = y := by
  apply MetricSpace.eq_of_dist_eq_zero


def a : ℕ → ℕ → ℝ := by
  intro n k
  exact (3*k)/3^n

#eval a

def b : ℕ → ℕ → ℝ := by
  intro n k
  exact (3*k+1)/3^n

lemma test : a 3 2 ≠  0 := by
  unfold a
  simp

def c : ℕ → ℕ → ℝ := by
  intro n k
  exact (3*k+2)/3^n

def d : ℕ → ℕ → ℝ := by
  intro n k
  exact (3*k+3)/3^n

lemma extremas_in_C (n :ℕ ) (k : ℕ ) :
(n ≠ 0 ) → ( k ≤ (3^(n-1) -1) ) →
((a n k)∈ Cantor_set ) ∧ ((b n k)∈ Cantor_set ) ∧ ((c n k)∈ Cantor_set ) ∧ ((d n k)∈ Cantor_set ) := by
 intro H1 H2
 sorry

lemma in_one_interval (x : ℝ ) :
(x ∈ Cantor_set ) → ( ∀ n :ℕ, (n ≠ 0) → (∃ k :ℕ,
( k ≤ (3^(n-1) -1) ) ∧
(( x ∈ Set.Icc (a n k) (b n k) ) ∨ ( x ∈ Set.Icc (c n k) (d n k) ) ) ) )  := by
  intro h n I
  sorry

lemma distance_n (n k :ℕ ) :
((n ≠ 0 ) ∧  ( k ≤ (3^(n-1) -1) )) →
( dist (a n k) (b n k) ≤ 1/3^n ) ∧ ( dist (c n k) (d n k) ≤ 1/3^n ) := by
  intro h
  sorry

lemma not_alone (n : ℕ ) (x : ℝ ) (h : n ≠ 0)  (h2 : x ∈ Cantor_set) :
(∃ y : ℝ, (y≠ x)∧ (y ∈ Cantor_set) ∧   (dist y x ≤ 1/3^n)) := by
  obtain ⟨ k , hk1, hk2⟩  := in_one_interval x h2 n h
  -- apply in_one_interval at h2
  cases hk2 with
  | inl h =>
    cases em  ( x = a n k) with
    | inl H =>
    use (b n k)
    rewrite [H]
    constructor
    unfold a n k
    simp
    unfold b n k

    · done
    · done
    | inr H => sorry

    sorry
  | inr h =>
    sorry

lemma Cantor_set_preperfect_isa : Preperfect Cantor_set := by
  rw [preperfect_iff_nhds]

  intro x h U hU
  rw [ Metric.mem_nhds_iff] at hU
  obtain ⟨ ε , epos, hball ⟩ := hU
  unfold Metric.ball at hball
  let n := Nat.ceil (Real.logb 3 ε )+1
  have He : 1/3^n < ε := by sorry --calcul log
  have non_0 : n≠ 0 := by simp
  obtain ⟨ y, Hy1, Hy2, Hy3 ⟩ := not_alone n x non_0 h
  use y
  constructor
  · refine Set.mem_inter ?_ Hy2
    refine hball ?_
    simp
    exact lt_of_le_of_lt Hy3 He

  · exact Hy1
