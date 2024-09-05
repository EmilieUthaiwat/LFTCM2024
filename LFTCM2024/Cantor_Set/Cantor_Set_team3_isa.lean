import LFTCM2024.Cantor_Set.Cantor_Team_3
import LFTCM2024.Cantor_Set.Cantor_Set
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Instances.ENNReal


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

--- from Tomas' file : triadic development

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
------------------------------------------
------------------------------------
-- some results about  the series ∑(n>= k) (2/3^n)
-----------------------------------------
------------------------------------------------

noncomputable def g := fun n:ℕ ↦ ((2/3^n) : ℝ)

lemma gpos : ∀ n, 0 ≤ g n := by
  intro n
  unfold g
  rw [div_nonneg_iff]
  left
  simp

noncomputable def g_part (k : ℕ ) : ℕ → ℝ  := fun n:ℕ ↦ (if n≤ k then  0 else g n)

lemma g_partineq (k : ℕ ) (n: ℕ) : (0 ≤ g_part k n) ∧ (g_part k n ≤ g n) := by
  unfold g_part
  aesop
  apply gpos
  apply gpos

lemma rec_g_part (k :ℕ ) : g_part (k+1) = fun n:ℕ ↦ (if n= k+1 then  0 else (g_part k) n) := by
  ext n
  by_cases H : (n ≤ k+1)
  . have I1 : g_part (k+1) n = 0 := by
      unfold g_part
      simp
      intro L
      linarith
  . have I1 : g_part (k+1) n = g n := by
      unfold g_part
      simp
      intro L
      linarith
    have I2 : g_part (k) n = g n := by
      unfold g_part
      simp
      intro L
      linarith
    aesop

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
  have H1 : (0 :ℝ)  ≤ 1/3 := by linarith
  have H2 :  (1:ℝ )/3 <1 := by linarith
  have K : (3/2 : ℝ) = (1 - 1/3)⁻¹ := by ring_nf
  rw [K]
  exact  geo_sum_r (1/3 : ℝ ) H1 H2

lemma geo_sum  : Summable (g) ∧ ( tsum g   = (3 :ℝ )) := by
  have geo3 : g = fun (n:ℕ) ↦ 2*(1/3 : ℝ )^n := by
    ext n
    unfold g
    ring_nf
  rw [geo3]
  and_intros
  · rw [summable_mul_left_iff (2)]
    apply geo_sum_third.1
  · rw [tsum_mul_left, geo_sum_third.2]
    ring

-----------------------------------------
--absent in my library ?? ----
theorem summable_of_nonneg_of_le {f g : β → ℝ} (hg : ∀ b, 0 ≤ g b) (hgf : ∀ b, g b ≤ f b)
    (hf : Summable f) : Summable g := by
  lift f to β → ℝ≥0 using fun b => (hg b).trans (hgf b)
  lift g to β → ℝ≥0 using hg
  rw [NNReal.summable_coe] at hf ⊢
  exact NNReal.summable_of_le (fun b => NNReal.coe_le_coe.1 (hgf b)) hf
----- to remove when in the library ?
-----------------------------------

lemma geo_sum_part (k : ℕ ) : Summable (g_part k) := by
  have H : ∀ n, g_part k n ≤ g n := by
    intro n
    exact (g_partineq k n).2
  have K : ∀ n, 0 ≤ g_part k n  := by
    intro n
    exact (g_partineq k n).1
  exact (summable_of_nonneg_of_le K H geo_sum.1)

lemma sum_geo_sum_part (k : ℕ ) : tsum (g_part k) = (1/3^k) := by
  induction (k :ℕ ) with
  | zero =>
    have hh : (2/3^0 :ℝ )=( 2 :ℝ):= by ring_nf
    have h0 : ∑' (n : ℕ), (g n) = 3 := by apply geo_sum.2
    have h1 : ∑' (n : ℕ), (g n) = g 0 + ∑' (n : ℕ), if n = 0 then 0 else (g n) :=
      by apply tsum_eq_add_tsum_ite geo_sum.1 0
    have h2 : 3 = 2 + ∑' (n : ℕ), if n = 0 then 0 else ((2/3^n) : ℝ) := by
      rw [h0] at h1
      unfold g at h1
      rw [hh] at h1
      exact h1
    have K : g_part 0 = fun (n:ℕ) ↦ (if n = 0 then 0 else ((2/3^n) : ℝ)):= by
      ext n
      unfold g_part
      simp
      unfold g
      eq_refl
    rw [K]
    have h3 : 1 = ∑' (n : ℕ), (if n = 0 then 0 else ((2/3^n) : ℝ)) := by linarith
    rw [← h3]
    simp
  | succ k ih =>
    have h0 : ∑' (n : ℕ), (g_part k n) = (1/3^k) := by apply ih
    have h1 : ∑' (n : ℕ), (g_part k (n)) = g_part k (k+1) + ∑' (n : ℕ), if n = (k+1) then 0 else (g_part k n) := by
      apply tsum_eq_add_tsum_ite (geo_sum_part (k)) (k+1)
    have K : g_part (k+1) = fun (n:ℕ) ↦ (if n = (k+1) then 0 else (g_part k) n ):= by apply rec_g_part (k)
    rw [K]
    rw [h0] at h1
    have hh : g_part k (k+1) = 2/3^(k+1) := by
        unfold g_part
        have hhh : ¬ (k+1 ≤ k ) := by simp
        simp_rw [hhh]
        simp
        unfold g
        eq_refl
    rw [hh] at h1
    have h2 : (1/3^k) - 2/3^(k+1) = ∑' (n : ℕ), if n = (k+1) then 0 else (g_part k n)  := by linarith
    rw [← h2]
    ring_nf
    rw [pow_succ]
    linarith

----------------------------------------------------------
-- proving that C = {∑ a_k/3^k, a_k =0 or 2}
------------------------------------------------------------

-- step 1 - Defining the set D_0 in term of set of sum of series

def isTriadic (b : ℕ → ℕ) : Prop := (∀ n, (b n = 0)∨ (b n = 1) ∨ (b n =2)) ∧ (b 0 =0)

noncomputable def fTriadic  (b : ℕ → ℕ) := fun n:ℕ ↦ (((b n)/3^n) : ℝ)

lemma fTriadic_ineq (b : ℕ → ℕ) :
isTriadic b → (∀ n, fTriadic b n ≤ g_part 0 n ) ∧(∀ n, 0 ≤ fTriadic b n) := by
  intro H
  unfold  fTriadic
  unfold isTriadic at H
  and_intros
  . intro n
    have K : (b n = 0)∨ (b n = 1) ∨ (b n =2) := by exact H.1 n
    have L : b 0 = 0 := by exact H.2
    by_cases J : (n= 0)
    . unfold g_part
      simp
      rw [J, L]
      simp
    . have J2 : g_part 0 n = g n := by
        unfold g_part
        simp
        intro k
        trivial
      rw [J2]
      unfold g
      cases K with
      | inl K1 =>
        rw [K1]
        ring_nf
        simp
      | inr K2  =>
        cases K2 with
        | inl K3 =>
          rw [K3]
          ring_nf
          simp
        | inr K4 =>
          rw [K4]
          ring_nf
          simp
  . intro n
    have K : (b n = 0)∨ (b n = 1) ∨ (b n =2) := by exact H.1 n
    cases K with
  | inl K1 =>
    rw [K1]
    ring_nf
    simp
  | inr K2  =>
    cases K2 with
    | inl K3 =>
      rw [K3]
      ring_nf
      simp
    | inr K4 =>
      rw [K4]
      ring_nf
      simp

lemma summable_fTriadic (b : ℕ → ℕ) :
isTriadic b → (Summable (fTriadic b)) := by
  intros H
  exact (summable_of_nonneg_of_le  (fTriadic_ineq b H).2 (fTriadic_ineq b H).1 (geo_sum_part 0))

lemma inUnit (b : ℕ → ℕ) :
isTriadic b →  (tsum (fTriadic b) ∈ Set.Icc 0 1) := by
  intros H
  and_intros
  ·  exact tsum_nonneg (fTriadic_ineq b H).2
  · have K : ∑' (n : ℕ ), (g_part 0) n =1 := by
      have K2 : ∑' (n : ℕ ), (g_part 0) n =1/3^0 := by exact sum_geo_sum_part 0
      have L:  1 = 1/ 3^0 := by ring_nf
      aesop
    rw [← K]
    exact tsum_le_tsum (fTriadic_ineq b H).1 (summable_fTriadic b H) (geo_sum_part 0)


def Dinit : Set ℝ :=
{ x : ℝ | ∃ b : ℕ → ℕ , (isTriadic b) ∧ (x=tsum (fTriadic b))}
#check Dinit
example (p q : Nat → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro h
  cases h with
  | intro x hpq =>
    cases hpq with
    | intro hp hq =>
      exists x

--- Step 2 - [0,1] = set of triadic series
def sub1 : Nat → Nat
  | 0   => 0
  | n+1 => n
#check sub1 0

noncomputable def triadic_partial (x : ℝ  ) : (ℕ → ℕ × ℝ )
  | 0 => (0,0)
  | n+1 => (Nat.floor (3^(n+1)*(x-(triadic_partial x n).2)),
  (triadic_partial x n).2+Nat.floor (3^(n+1)*(x-(triadic_partial x n).2))/3^(n+1))

#check triadic_partial 1 1
#check (0,0).2
#check Nat.floor (1 :ℝ)

noncomputable def y (x : ℝ  ) := fun n :ℕ ↦ (triadic_partial x n).2
noncomputable def b (x : ℝ  ) := fun n :ℕ ↦ (triadic_partial x n).1

lemma prop_yb (x : ℝ ) (n : ℕ) (h : x∈ Set.Icc 0 1):
 (y x n ≤ x) ∧ (x ≤  y x n + 1/3^n) ∧ (0 ≤ b x n) ∧ ( b x n ≤ 2) := by
  induction n with
  | zero =>
    unfold y b
    unfold triadic_partial
    simp
    simp_rw [←  Set.mem_Icc, h]
  | succ n ih =>
     cases' ih with h1 h2
     cases' h2 with h2 h3
     cases' h3 with h3 h4
     have K : y x (Nat.succ n) = y x n + (b x (n+1))/3^(Nat.succ n) := by
      unfold b y
      tauto

     have j :  0< 3^(n+1) := by simp
     have J0 : Nat.floor (3^(n+1)*(x-(triadic_partial x n).2)) ≤ 3^(n+1)*(x - (y x n)) := by
      apply Nat.floor_le
      unfold y at h1
      --have j : 0 ≤ 3^(n+1) := by simp
      have jj : 0 ≤ x-(triadic_partial x n).2 := by linarith
      simp
      linarith
     have J00 : b x (n+1) ≤ 3^(n+1)*(x - (y x n)) := by exact J0
     have J1 : b x (n+1) ≤ 3^(n+1)*x - 3^(n+1)*(y x n) := by linarith
     have J20 : 3^(n+1)*(x - (y x n))<  Nat.floor (3^(n+1)*(x-(triadic_partial x n).2))+1 := by
        apply Nat.lt_floor_add_one
     have J200 :  3^(n+1)*(x - (y x n))<  b x (n+1) +1 := by exact J20
     --have J10 : 3^(n+1)*x - 3^(n+1)*(y x n)≤  b x (n+1) +1  := by linarith
     have J2 :  3^(n+1)*x - 3^(n+1)*(y x n) ≤ b x (n+1) +1 := by linarith
     have J3 : 3 ^ (n + 1) * (y x n) + ↑(b x (n + 1)) ≤ 3 ^ (n + 1) * x  := by
          linarith
     rw [K]
     and_intros
     ·
       have J32 : (3 ^ (n + 1) * (y x n) + ↑(b x (n + 1)))/3^(n+1) ≤ (3 ^ (n + 1) *  x)/3^(n+1)  := by

         sorry
       have J4 : (y x n) + ↑(b x (n + 1))/3^(n+1) ≤ x  := by

        sorry
       exact J4

     ·--linarith
      sorry
     ·linarith

     · --linarith
        sorry




#check Set.mem_Icc

lemma eqDinitUnit : Dinit = Set.Icc 0 1 := by
  ext x
  constructor
  · intro H
    unfold Dinit at H
    cases H with
    | intro b h =>
      cases h with
    | intro hp hq =>
      rw [hq]
      exact inUnit b hp
  . intro H
    unfold Dinit
    simp
    --- b to construct b n = floor (bla bla)
    sorry


-- step 3 - Defining the set D_n (=C_n) in term of sets of sum of series

def preESet : ℕ → Set ℝ -- useless ?
  | 0 => Dinit
  | Nat.succ n => T_L '' preESet n ∪ T_R '' preESet n
def ESet := iInf preESet

def isTriadicCantor (b : ℕ → ℕ) (k : ℕ ) : Prop := (isTriadic b) ∧(∀ n ≤ k, (b n = 0) ∨ (b n =2))

def DSet (n: ℕ ) : Set ℝ :=
if n=0 then Dinit else { x : ℝ | ∃ b : ℕ → ℕ , (isTriadicCantor b n) ∧ (x=tsum (fTriadic b))}

lemma  eqDSet {x : ℝ }(n : ℕ )   : x ∈ DSet (n+1) ↔ x ∈  T_L '' DSet n ∪ T_R '' DSet n := by
  apply Iff.intro
  · intro H
    sorry
  · intro H
    apply Or.elim H
    . intro H1
      sorry
    . intro H2
      sorry


lemma same_sets (n : ℕ ) : preESet n = DSet n := by
  unfold DSet
  unfold preESet
  induction n with
  | zero =>
    simp
  | succ n ih =>

    sorry










----------------------------------------------------
-- premiers essais sur bijection entre Cantor set et {0,1}^N

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
   have L : (2:ℝ ) ≤ 3^n := by linarith
   rw [@div_le_one_iff]
   left
   and_intros
   . simp
   . exact L
   | true =>
   simp


lemma summable_map  (f : ℕ → Bool) : Summable (map_to_real f) := by
  apply Summable.of_norm_bounded g geo_sum.1
  intro i
  unfold g map_to_real
  ring_nf
  cases f i with
  | false =>
    simp
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






















-----------------------------------------------------------
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
