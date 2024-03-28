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


lemma extremuses_of_Cantor_set  (x : Cantor_set) (n :ℕ) (hp: x≠ 0) :
(((Nat.ceil (x.1*3^n))/3^n):ℝ)∈ Cantor_set∧ (((Nat.ceil (x.1*3^n) -1)/3^n):ℝ) ∈ Cantor_set :=
by
  suffices hfin : ∀ m ∈ ℕ,
  ((Nat.ceil (x.1*3^n))/3^n) ∈ Cantor_set_Union_Icc m
  ∧ ((Nat.ceil (x.1*3^n)-(1) : ℕ)/3^n) ∈ Cantor_set_Union_Icc m by
    intro m
    sorry



  --(((Nat.ceil (x.1*3^n))/3^n):ℝ)∈ Cantor_set∧ (((Nat.floor (x.1*3^n) : ℕ)/3^n):ℝ) ∈

  have Cantor_set : Set ℝ := by
    sorry
  have hk :  ∃ k : ℕ ,
  (x∈ ((Set.Icc (3*k/3^n) (3*k+1/3^n) ∪ Set.Icc (3*k+2/3^n) (3*k+3/3^n)) : Set ℝ)) := by
    sorry
  rintro hk with (hk1 | hk2)


  sorry

lemma LZCantor_set_preperfect : Preperfect Cantor_set := by
  rw [preperfect_iff_nhds]

  intro x hx U hU
  rw [ Metric.mem_nhds_iff] at hU
  obtain ⟨ ε , epos, hball ⟩ := hU
  let n : ℕ  := (Nat.ceil (Real.logb 3 (1/ε)))+1
  set y : ℝ := ((Nat.ceil (x*3^n))/3^n) with hy1
  by_cases hy : y≠ x
  · have : y∈ U∩ Cantor_set := by
      constructor
      · apply hball
        simp
        have ineq : 3^(-(n:ℤ))<ε := by
          simp

          sorry
        apply lt_trans ?_ ineq
        rw[hy1]
        -- Nat.lt_floor_add_one CANII

        rw[Int.ceil_lt_add_one]
        sorry
      · apply (extremuses_of_Cantor_set ⟨x, hx⟩ n).1
    use y
  · let z : ℝ := ((Nat.floor (x*3^n))/3^n)  --(Nat.ceil (x*3^n)-(1) : ℕ)/3^n
    have : z∈ U∩ Cantor_set := by
      constructor
      · apply hball
        simp
        sorry
      ·
        apply (extremuses_of_Cantor_set ⟨x, hx⟩ n).2
    have : z≠ x := by
      push_neg at hy
      rw[hy.symm]
      aesop
    use z
