import LFTCM2024.Cantor_Set.Cantor_Team_3

lemma Is_TotallyDisconnected_Cantor_attempt2 : IsTotallyDisconnected Cantor_set := by
  intro S hS h₁S x h₁x y h₁y
  by_contra nhxy
  unfold IsPreconnected at h₁S
  rcases (lt_trichotomy x y) with xsmallery | ysmallerx
  · have hd : ∃ N : ℕ, 1/(3^N) < |(y:ℝ) - (x:ℝ)| := by
      have usefulfact := exists_pow_lt_of_lt_one (x := |(y:ℝ) - (x:ℝ)|) (y := (1/3 : ℝ))
      simp only [abs_pos, ne_eq, one_div, inv_pow] at usefulfact
      simp only [one_div]
      apply usefulfact
      · rw [@sub_eq_zero]
        intro heq
        subst y
        apply nhxy
        rfl
      · norm_num
    have hxy : |y - x| < 1 := by sorry
    obtain ⟨N, hN⟩ := hd
    obtain ⟨z, hz⟩ : ∃ z : ℝ, z ∉ Cantor_set ∧ x < z ∧ z < y := by
     use x+1/(2*3^N)
     constructor
     · sorry
     · constructor
       · simp only [one_div, mul_inv_rev, lt_add_iff_pos_right, gt_iff_lt, inv_pos, Nat.ofNat_pos,
         pow_pos, mul_pos_iff_of_pos_left]
       · ring_nf
         ring_nf at hN
         have hTemporary : x + |y - x| * (1 / 2) < y := by
          have hModule : |y - x| = y - x := by
            simp only [abs_eq_self, sub_nonneg]
            exact le_of_lt xsmallery
          rw [hModule]
          linarith
         have hTemporary2 : x + (1 / 3) ^ N * (1 / 2) < x + |y - x| * (1 / 2) := by
          simp only [one_div, inv_pow, add_lt_add_iff_left, gt_iff_lt, inv_pos, Nat.ofNat_pos,
            mul_lt_mul_right]
          rw [@one_div] at hN
          simp only [inv_pow] at hN
          assumption
         apply lt_trans hTemporary2
         assumption

    -- use z= x + 1/2*3^N
    set A := Set.Iio z
    set B := Set.Ioi z
    have bla : ¬ Set.Nonempty (S ∩ (A ∩ B)) := by
     refine Set.not_nonempty_iff_eq_empty.mpr ?_
     rw [@Set.Iio_inter_Ioi]
     simp only [gt_iff_lt, lt_self_iff_false, not_false_eq_true, Set.Ioo_eq_empty, Set.inter_empty]
    apply bla
    apply h₁S
    ·apply isOpen_Iio
    ·apply isOpen_Ioi
    · rw [@Set.subset_def]
      intro x' hx'S
      rw [@Set.mem_union]
      simp [A, B]
      intro heq
      subst z
      apply hz.1
      apply hS
      apply hx'S
    · use x
      constructor
      apply h₁x
      apply hz.2.1
    · use y
      constructor
      apply h₁y
      apply hz.2.2
  · rcases ysmallerx with h1 | h2
    · apply nhxy
      assumption
    · have hd : ∃ N : ℕ, 1/(3^N) < |x - y| := by
        have usefulfact := exists_pow_lt_of_lt_one (x := |x - y|) (y := (1/3 : ℝ))
        simp only [abs_pos, ne_eq, one_div, inv_pow] at usefulfact
        simp only [one_div]
        apply usefulfact
        · rw [@sub_eq_zero]
          intro heq
          subst y
          apply nhxy
          rfl
        · norm_num
      have hxy : |(y:ℝ) - (x:ℝ)| < 1 := by sorry
      obtain ⟨z, hz⟩ : ∃ z : ℝ, z ∉ Cantor_set ∧ y < z ∧ z < x := by sorry
      -- use z= y + 1/2*3^N
      set A := Set.Iio z
      set B := Set.Ioi z
      have bla : ¬ Set.Nonempty (S ∩ (A ∩ B)) := by
        refine Set.not_nonempty_iff_eq_empty.mpr ?_
        rw [@Set.Iio_inter_Ioi]
        simp only [gt_iff_lt, lt_self_iff_false, not_false_eq_true, Set.Ioo_eq_empty, Set.inter_empty]
      apply bla
      apply h₁S
      ·apply isOpen_Iio
      ·apply isOpen_Ioi
      ·rw [@Set.subset_def]
       intro y' hy'S
       rw [@Set.mem_union]
       simp [A, B]
       intro heq
       subst z
       apply hz.1
       apply hS
       apply hy'S
      · use y
        constructor
        apply h₁y
        apply hz.2.1
      · use x
        constructor
        apply h₁x
        apply hz.2.2
