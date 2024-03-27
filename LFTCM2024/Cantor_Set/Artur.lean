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
  · sorry
  · rcases h2 with h1 | h2
    · apply nhxy
      assumption
    · sorry
