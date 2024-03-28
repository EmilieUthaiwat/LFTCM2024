import LFTCM2024.Cantor_Set.Cantor_Team_3

-- --lemma Cantor_set_preperfect : Preperfect Cantor_set := by --no isolated points
--   intro x
--   intro hx
--   let ε : ℝ
--     let n : ℕ, n>
--   by
--     done
-- lemma extremuses_of_Cantor_set (n:ℕ) (k:ℕ) (i:ℕ) (h : k≤ 3^(n-1)-1)(hi : i≤ 3) :
--   ((((k+i) : ℝ)/(3^n)) ∈ Cantor_set) := by
--     suffices this : ∀ m : ℕ, (((k+i) : ℝ)/(3^n))∈ pre_Cantor_set m by
--       simp [Cantor_set, this]
--     intro m
--     induction m with
--     | zero =>
--         unfold pre_Cantor_set
--         simp
--         constructor
--         · positivity
--         · refine (div_le_one ?_).mpr ?_
--           positivity
--           norm_cast

--     | succ n ih =>
--       --((k : ℝ)/(3^n))
--       unfold pre_Cantor_set
--       r (hL , hR)
--       sorry

-- lemma Ceil_minus_one_aux (x : ℝ) : |⌈-x⌉ + x| < 1 := by
--   rw [Int.ceil_neg, add_comm, Int.cast_neg]
--   apply Int.abs_sub_lt_one_of_floor_eq_floor
--   simp

-- lemma Ceil_minus_one (x : ℝ) : |⌈x⌉ - x| < 1 := by
--   have h : _ := Ceil_minus_one_aux (- x)
--   simpa using h
lemma foo (hx : x ∈  Cantor_set) (n :ℕ) (hnice : ∀ a<n, x≠ (a:ℝ)/3^n) :
∀m<n, (((Nat.floor (x*3^n))/3^n):ℝ)∈ Set.Icc (((Nat.floor (x*3^m))/3^m):ℝ) (((Nat.floor (x*3^m))/3^m):ℝ) := by
sorry

lemma extremuses_of_Cantor_set_nice_x  (hx : x ∈  Cantor_set) (n :ℕ) (hnice : ∀ a<n, x≠ (a:ℝ)/3^n) :
(((Nat.floor (x*3^n))/3^n):ℝ)∈ Cantor_set :=--∧ (((Nat.ceil (x.1*3^n))/3^n):ℝ) ∈ Cantor_set :=
by
suffices h1:  ∀ m :ℕ,  ((((Nat.floor (x*3^n))/3^n):ℝ)∈ Cantor_set_Union_Icc m) from by
  done
by_cases hm : m≥ n
· sorry
· sorry
sorry

noncomputable
def function_extremuses_Cantor_set(n:ℕ):  Cantor_set → Cantor_set :=
  fun x =>
  if (((Nat.floor (x.1*3^n))/3^n):ℝ)==x
    then sorry
  else
    have p : ∃ k≤ 3^(n-1)-1, x∈ (Set.Icc ((3*k)/3^n) ((3*k+1)/3^n) ∪ Set.Icc ((3*k+2)/3^n) ((3*k+3)/3^n)) := by
      sorry
    let h := p.1
  ⟨(3*h)/3^n⟩
  sorry

lemma extremuses_of_Cantor_set  (x : Cantor_set) (n :ℕ) :
(((Nat.floor (x.1*3^n))/3^n):ℝ)∈ Cantor_set∧ (((Nat.ceil (x.1*3^n))/3^n):ℝ) ∈ Cantor_set :=
by
  sorry
  -- suffices hfin : ∀ m ∈ ℕ,
  -- ((Nat.ceil (x.1*3^n))/3^n) ∈ Cantor_set_Union_Icc m
  -- ∧ ((Nat.ceil (x.1*3^n)-(1) : ℕ)/3^n) ∈ Cantor_set_Union_Icc m by
  --   intro m
  --   sorry



  -- --(((Nat.ceil (x.1*3^n))/3^n):ℝ)∈ Cantor_set∧ (((Nat.floor (x.1*3^n) : ℕ)/3^n):ℝ) ∈

  -- have Cantor_set : Set ℝ := by
  --   sorry
  -- have hk :  ∃ k : ℕ ,
  -- (x∈ ((Set.Icc (3*k/3^n) (3*k+1/3^n) ∪ Set.Icc (3*k+2/3^n) (3*k+3/3^n)) : Set ℝ)) := by
  --   sorry
  -- rintro hk with (hk1 | hk2)


  -- sorry




lemma LZCantor_set_preperfect : Preperfect Cantor_set := by
  rw [preperfect_iff_nhds]

  intro x hx U hU
  rw [ Metric.mem_nhds_iff] at hU
  obtain ⟨ ε , epos, hball ⟩ := hU
  let n : ℕ  := (Nat.ceil (Real.logb 3 (1/ε)))+1
  have hnε : 3^(-(n:ℤ))<ε := by
          simp
          sorry  --calculations....
  set y : ℝ := ((Nat.ceil (x*3^n))/3^n) with hy1
  by_cases hy : y≠ x
  · have : y∈ U∩ Cantor_set := by
      constructor
      · apply hball
        simp

        apply lt_trans ?_ ineq
        rw[hy1]

        --Int.ceil_lt_add_one  --calculations...
        sorry
      · apply (extremuses_of_Cantor_set ⟨x, hx⟩ n).2
    use y
  · let z : ℝ := ((Nat.floor (x*3^n))/3^n)  --(Nat.ceil (x*3^n)-(1) : ℕ)/3^n
    have : z∈ U∩ Cantor_set := by
      constructor
      · apply hball
        simp
        sorry --calculation...
      · apply (extremuses_of_Cantor_set ⟨x, hx⟩ n).1

    have : z≠ x := by
      push_neg at hy
      rw[hy.symm]
      sorry
    use z

lemma Cantor_set_tot_disc' : TotallyDisconnectedSpace Cantor_set := by
  apply (totallyDisconnectedSpace_iff Cantor_set).2
  intro S hS h₁S x h₁x y h₁y
  by_contra nhxy
  unfold IsPreconnected at h₁S
  have h : x < y ∨ x = y ∨ y < x := by
    exact lt_trichotomy x y
  rcases (lt_trichotomy x y) with xsmallery | ysmallerx
  · have hN : ∃ N : ℕ, N > 0 ∧ 1/ (3^N) < |(y:ℝ) - (x:ℝ)| := by sorry
    obtain ⟨z, hz⟩ : ∃ z : ℝ, z ∉ Cantor_set ∧ x < z ∧ z < y := by sorry
    -- use z= x + 1/2*3^N
    set A : Set Cantor_set := {x | (x: ℝ) ∈ Set.Ioo -1 z}
    set B : Set Cantor_set := {x | (x: ℝ) ∈ Set.Ioo z 2}
    have hfinal_1 : IsOpen A ∧ IsOpen B ∧ Cantor_set ⊆ A ∪ B ∧ Set.Nonempty (Cantor_set ∩ A) ∧
       Set.Nonempty (Cantor_set ∩ B) := by
        refine ⟨?_,?_,?_,?_⟩
        · exact?
          sorry
        · sorry
        ·
          sorry
        · constructor
          · use x
            constructor
            · exact Subtype.coe_prop x
            · refine Set.mem_image_of_mem Subtype.val ?h.right.h

              exact hz.2.1
          · use y
          sorry
    have bla : ¬ Set.Nonempty (S ∩ (A ∩ B)) := by
      suffices
       sorry
    apply bla
    apply h₁S
    · sorry
    · sorry
    · sorry
    · sorry
    · sorry
  · rcases ysmallerx with h1 | h2
    · apply nhxy
      assumption
    · sorry
  sorry
