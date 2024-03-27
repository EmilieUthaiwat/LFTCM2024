import LFTCM2024.Cantor_Set.Cantor_Team_3

lemma Cantor_set_tot_disc' : TotallyDisconnectedSpace Cantor_set := by
  apply (totallyDisconnectedSpace_iff Cantor_set).2
  intro S hS h₁S x h₁x y h₁y
  by_contra nhxy
  unfold IsPreconnected at h₁S
  have h : x < y ∨ x = y ∨ y < x := by
    exact lt_trichotomy x y
  --obtain (h1 | h2) := h
  rcases (lt_trichotomy x y) with h1 | h2
  · have hd : ∃ N : ℕ, N > 0 ∧ 1/ (3^N) < |(y:ℝ) - (x:ℝ)| := by sorry
    obtain ⟨z, hz⟩ : ∃ z : ℝ, z ∉ Cantor_set ∧ x < z ∧ z < y := by sorry
    -- use z= x + 1/2*3^N
    have A := Set.Ioo 0 z
    have B := Set.Ioo z 1
    have hfinal_1 : IsOpen A ∧ IsOpen B ∧ Cantor_set ⊆ A ∪ B ∧ Set.Nonempty (Cantor_set ∪ A) ∧ Set.Nonempty (Cantor_set ∪ B) := by sorry
    have bla : ¬ Set.Nonempty (Cantor_set ∩ (A ∩ B)) := by sorry
    sorry
  · rcases h2 with h1 | h2
    · apply nhxy
      assumption
    · sorry

#check Set.Ioo
