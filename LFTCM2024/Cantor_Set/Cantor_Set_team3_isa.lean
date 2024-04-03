import LFTCM2024.Cantor_Set.Cantor_Team_3
import LFTCM2024.Cantor_Set.Cantor_Set
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum

-- import Mathlib.Topology.MetricSpace.Basic

-- instance Cantor_set.metricSpace : MetricSpace Cantor_set :=
--  Subtype.metricSpace



lemma obvious_inclusion : Cantor_set ⊆ Set.Icc 0 1 := by
  intro x
  unfold Cantor_set
  intro h
  simp only [Set.iInf_eq_iInter, Set.mem_iInter] at h
  exact h 0

----------------------------

--- from Tomas' file : tryadic development

lemma map_to_product (x : ℝ) : (ℕ → Bool) := by
  intro n
  let p := x ∈ T_L '' pre_Cantor_set n
  classical
  -- let d : Decidable p := by
  --   by_cases c : p   -- use excluded middle on p
  --   · exact isTrue c
  --   · exact isFalse c
  exact decide p

#check map_to_product
#check pre_Cantor_set

noncomputable def g := fun n:ℕ ↦ ((2/3^n) : ℝ)
noncomputable def g_part (k : ℕ ) : ℕ → ℝ  := fun n:ℕ ↦ (if n≤ k then  0 else g n)
--variable (k : ℕ)
#check (g_part 0 0)

lemma geo_sum_r (r: ℝ ) (h1 : 0≤ r) (h2 : r<1) :
Summable  ( fun(n:ℕ) =>r^n  ) ∧ ( tsum ( fun(n:ℕ) =>r^n  ) = (1 - r)⁻¹ ) := by
  and_intros
  . exact summable_geometric_of_lt_one h1 h2
  . have H : ‖ r‖ <1 := by
     simp
     rw [abs_of_nonneg h1]
     exact h2
    exact tsum_geometric_of_norm_lt_one H

lemma geo_sum_third :
(Summable fun (n:ℕ) =>(1/3 : ℝ )^n) ∧ ( tsum ( fun(n:ℕ) =>(1/3 : ℝ )^n  ) = (3 :ℝ )/2 ) := by
  have H1 : (0 :ℝ)  ≤ 1/3 := by
    ring_nf
    simp
  have H2 :  (1:ℝ )/3 <1 := by
    rw [@div_lt_one_iff]
    left
    simp
  have K : (3/2 : ℝ) = (1 - 1/3)⁻¹ := by ring_nf
  rw [K]
  exact  geo_sum_r (1/3 : ℝ ) H1 H2


lemma geo_sum  : Summable (g) := by sorry
lemma geo_sum_part (k : ℕ ) : Summable (g_part k) := by sorry
lemma sum_geo_sum_part (k : ℕ ) : tsum (g_part k) = (1/3^k) := by sorry

noncomputable def map_to_real : (f : ℕ → Bool) → (ℕ → ℝ)  :=  by
  intro f n
  if f n then exact (0/3^n)
  else exact (2/3^n)

lemma inequalities_map_to_real  (f : ℕ → Bool) (n : ℕ) (h : f 0 = true):
(0 ≤ (map_to_real f n))∧ (map_to_real f n ≤ 1) := by
  and_intros
  · unfold map_to_real
    cases f n with
  | false =>
    simp
    ring_nf
    simp
  | true =>
    simp
  · unfold map_to_real
    by_cases H:( n =0)
    · rw [H,h]
      simp
    · cases f n with
   | false =>
   simp
   have J : 1 ≤ n := by
    rw [@Nat.one_le_iff_ne_zero]
    exact H
   have K : (3^1:ℝ ) ≤ 3^n := by
    rw [pow_le_pow_iff_right]
    exact J
    simp
   have L : (2:ℝ ) ≤ 3^n := by
     have : ((2: ℝ) ≤ 3^1) := by
      simp
      rw [@Nat.ofNat_le]
      simp
     apply transitive_le
     · exact this
     · exact K
   rw [@div_le_one_iff]
   left
   and_intros
   . simp
   . exact L
   | true =>
   simp


lemma summable_map  (f : ℕ → Bool) : Summable (map_to_real f) := by
  apply Summable.of_norm_bounded g geo_sum
  intro i
  unfold g
  unfold map_to_real
  simp
  ring_nf
  cases f i with
  | false =>
    simp
    have h : |((3 :ℝ ) ^ i)⁻¹ * 2| =(3 ^ i)⁻¹ * 2 := by
      simp
    rw [h]
  | true =>
    simp

noncomputable def fCS (f : ℕ → Bool) : ℝ  := tsum (map_to_real f)
#check fCS

lemma test_zero {f : ℕ → Bool} (h : ∀ n, f n = true) : fCS f =0 := by
  unfold fCS
  have k : ∀ n, (map_to_real f) n =0 := by
    unfold map_to_real
    intro n
    simp
    refine (h n)
  --have i : tsum (fun (n : ℕ) ↦ (0 : ℝ) ) =0 := by apply tsum_zero
  have j : (map_to_real f)=(fun (n : ℕ) ↦ (0 : ℝ) ) := by
    ext n
    exact k n
  rw [j]
  exact tsum_zero

#check true≤ false


lemma fCS_is_everywhere (f : ℕ → Bool) (h : f 0 = true):
∀ n : ℕ, (fCS f) ∈ pre_Cantor_set n := by
  intro n
  induction n with
  | zero =>
    simp [pre_Cantor_set]
    unfold fCS
    have I : ∀ m :ℕ, 0 ≤ map_to_real f m := by
      intro m
      apply (inequalities_map_to_real f m h).1
    and_intros
    . sorry
    . sorry
  --theorem tsum_le_tsum {ι : Type u_1} {α : Type u_3} [OrderedAddCommMonoid α] [TopologicalSpace α] [OrderClosedTopology α] {f : ι → α} {g : ι → α} (h : ∀ (i : ι), f i ≤ g i) (hf : Summable f) (hg : Summable g) :
--∑' (i : ι), f i ≤ ∑' (i : ι), g i

  | succ n ih =>
    --  goal: ∃ x, x ∈ pre_Cantor_set n ∧ T_L x = 0
    --exact Or.inl ⟨0, ih, by unfold T_L; simp ⟩
    sorry

lemma map_to_CS (f : ℕ → Bool) (h : f 0 = true) : (fCS f) ∈ Cantor_set := by
  simp only [Cantor_set, iInf, Set.sInf_eq_sInter, Set.sInter_range, Set.mem_iInter]
  exact fCS_is_everywhere f h


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



noncomputable def dev : Cantor_set →  (ℕ → ℕ ) := by
  intro x n
  if map_to_product x n then exact 0
  else exact 2

noncomputable def dev_bool :  (ℕ → ℕ ) → (ℕ → Bool) := by
  intro a n
  if (a n =0) then exact true
  else exact false

noncomputable def inv_dev :  (ℕ → ℕ ) → ℝ  := by
  intro a
  if map_to_product x n then exact 0
  else exact 2


--- not isolated points via tryadic development

lemma Cantor_set_preperfect_tryadic_proof : Preperfect Cantor_set := by
  rw [preperfect_iff_nhds]
  intro x h U hU
  rw [ Metric.mem_nhds_iff] at hU
  obtain ⟨ ε , epos, hball ⟩ := hU
  unfold Metric.ball at hball
  let n := Nat.ceil (Real.logb 3 ε )+1
  have He : 1/3^n < ε := by sorry --calcul log
  have non_0 : n≠ 0 := by simp

  sorry


--- Lorenzo

lemma foo (hx : x ∈  Cantor_set) (n :ℕ) (hnice : ∀ a<n, x≠ (a:ℝ)/3^n) :
∀m<n, (((Nat.floor (x*3^n))/3^n):ℝ)∈ Set.Icc (((Nat.floor (x*3^m))/3^m):ℝ) (((Nat.floor (x*3^m))/3^m):ℝ) := by
sorry

lemma extremuses_of_Cantor_set_nice_x  (hx : x ∈  Cantor_set) (n :ℕ) (hnice : ∀ a<n, x≠ (a:ℝ)/3^n) :
(((Nat.floor (x*3^n))/3^n):ℝ)∈ Cantor_set :=- by
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
