import Mathlib.Analysis.Calculus.ContDiff.Basic
import LFTCM2024.Cantor_Set.Cantor_Team_3


/--noncomputable
def T_L (x : ℝ) : ℝ := x/3

noncomputable
def T_R (x : ℝ) : ℝ := (2+x)/3

def pre_Cantor_set : ℕ → Set ℝ
  | 0 => Set.Icc 0 1
  | Nat.succ n => T_L '' pre_Cantor_set (n) ∪ T_R '' pre_Cantor_set (n)

def Cantor_set := iInf pre_Cantor_set --/



lemma zero_in_pre_Cantor_set_0 : (0 : ℝ) ∈ pre_Cantor_set 0:= by
unfold pre_Cantor_set
apply unitInterval.zero_mem

lemma Induction_step (n : ℕ): (0 : ℝ) ∈ pre_Cantor_set (n) → (0 : ℝ) ∈ pre_Cantor_set (n+1):= by
intro h
unfold pre_Cantor_set
simp only [Nat.add_eq, add_zero, Set.mem_union, Set.mem_image]
left
use 0
constructor
· exact h
· unfold T_L
  rw [@zero_div]



lemma zero_in_pre_Cantor_set (n : ℕ ) : (0 : ℝ) ∈ pre_Cantor_set n:= by
 induction n with
   | zero => apply zero_in_pre_Cantor_set_0
   | succ n h =>
     apply Induction_step (n)
     exact h

 lemma zero_in_Cantor : 0 ∈ Cantor_set := by
 unfold Cantor_set
 simp only [Set.iInf_eq_iInter, Set.mem_iInter]
 apply zero_in_pre_Cantor_set

#check Set.Icc (0 : ℝ) (1 : ℝ)
#check Cantor_set

#check IsCompact

lemma bla: IsCompact (Set.Icc 0 1 : Set ℝ) :=
 isCompact_Icc

#check unitInterval

--lemma nla: IsCompact.Cantor_set

--IsCompact.{u_1} {X : Type u_1} [inst✝ : TopologicalSpace X] (s : Set X) : Prop


lemma Cantor_set_closed' : IsClosed Cantor_set  := by
  have h : ∀ n, IsClosed (pre_Cantor_set n) := by
    intro n
    induction n with
    | zero =>
      exact isClosed_Icc
    | succ n ih =>
      refine IsClosed.union ?_ ?_
      · refine (ClosedEmbedding.closed_iff_image_closed ?succ.refine_1.hf).mp ih
        apply Homeomorph.closedEmbedding Homeomorph_T_L
      · refine (ClosedEmbedding.closed_iff_image_closed ?succ.refine_2.hf).mp ih
        apply Homeomorph.closedEmbedding Homeomorph_T_R
  apply isClosed_iInter
  exact h

lemma Is_TotallyDisconnected_Cantor : IsTotallyDisconnected Cantor_set := by
  intro S hS h₁S x h₁x y h₁y
  by_contra nhxy
  unfold IsPreconnected at h₁S
  rcases (lt_trichotomy x y) with xsmallery | ysmallerx
  · have hN : ∃ N : ℕ, N > 0 ∧ 1/ (3^N) < |y - x| := by sorry
    obtain ⟨z, hz⟩ : ∃ z : ℝ, z ∉ Cantor_set ∧ x < z ∧ z < y := by sorry
    -- use z= x + 1/2*3^N
    set A := Set.Iio z
    set B := Set.Ioi z
    have bla : ¬ Set.Nonempty (S ∩ (A ∩ B)) := by sorry
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
    · have hN : ∃ N : ℕ, N > 0 ∧ 1/ (3^N) < |x - y| := by sorry
      obtain ⟨z, hz⟩ : ∃ z : ℝ, z ∉ Cantor_set ∧ y < z ∧ z < x := by sorry
      -- use z= y + 1/2*3^N
      set A := Set.Iio z
      set B := Set.Ioi z
      have bla : ¬ Set.Nonempty (S ∩ (A ∩ B)) := by sorry
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


lemma obvious_inclusion : Cantor_set ⊆ Set.Icc 0 1 := by
  intro x
  unfold Cantor_set
  intro h
  simp only [Set.iInf_eq_iInter, Set.mem_iInter] at h
  exact h 0


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
    have hxy : |y - x| < 1 := by
      have hx : 0 ≤ x ∧ x ≤ 1 := by
        have h : x ∈ Cantor_set := by apply hS; exact h₁x
        apply obvious_inclusion at h
        simp at h
        exact h

      have hy : 0 ≤ y ∧ y ≤ 1 := by
        have h : y ∈ Cantor_set := by apply hS; exact h₁y
        apply obvious_inclusion at h
        simp at h
        exact h

      rw [abs_sub_lt_iff]

      have ineq : -1 ≤ x - y ∧ x - y ≤ 1 := ⟨ by linarith, by linarith ⟩

      have abs_ineq : |x-y| ≤ 1 := by 
        rw [abs_le]
        exact ineq

      have abs_neq : |x-y| ≠ 1 := by
        intro h
        let A := Set.Iio (1/2 : ℝ)
        let B := Set.Ioi (1/2 : ℝ)

        have hz : 1/2 ∉ Cantor_set := by 
          sorry

        have S_sue_AB : S ⊆ A ∪ B := by
          rw [Set.subset_def]
          intro u hu
          have t : u ≠ 1/2 := by
            intro as
            subst u
            apply hS at hu
            exact hz hu

          rw [@Set.mem_union]
          rw [@Set.mem_Iio, @Set.mem_Ioi]
          norm_num
          use t

        have int_not_empty : ¬ Set.Nonempty (S ∩ (A ∩ B)) := by
          refine Set.not_nonempty_iff_eq_empty.mpr ?_
          rw [@Set.Iio_inter_Ioi]
          simp only [gt_iff_lt, lt_self_iff_false, not_false_eq_true, Set.Ioo_eq_empty, Set.inter_empty]

        apply int_not_empty

        apply h₁S
        · apply isOpen_Iio
        · apply isOpen_Ioi
        · exact S_sue_AB
        · sorry
        · sorry

      sorry

    obtain ⟨N, hN⟩ := hd
    obtain ⟨z, hz⟩ : ∃ z : ℝ, z ∉ Cantor_set ∧ x < z ∧ z < y := by
     use x+1/2*3^N
     sorry
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

/--lemma Cantor_set_tot_disc' : TotallyDisconnectedSpace Cantor_set := by
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
    set A : Set Cantor_set := {x | (x: ℝ) ∈ Set.Ioo 0 z}
    set B : Set Cantor_set := {x | (x: ℝ) ∈ Set.Ioo z 1}
    have hfinal_1 : IsOpen A ∧ IsOpen B ∧ Cantor_set ⊆ A ∪ B ∧ Set.Nonempty (Cantor_set ∪ A) ∧
       Set.Nonempty (Cantor_set ∪ B) := by sorry
    have bla : ¬ Set.Nonempty (S ∩ (A ∩ B)) := by sorry
    apply bla
    apply h₁S
    · apply isOpen_induced
      apply isOpen_Ioo
    · apply isOpen_induced
      apply isOpen_Ioo
    · rw [@Set.subset_def]
      intro x hS
      rw [@Set.mem_union]
      have xcomparez : (x:ℝ) ∈ Set.Ioo 0 z ∨ (x: ℝ) ∈ Set.Ioo z 1 := by
        have Cantor_subSet_Icc : Cantor_set ⊂ Set.Icc 0 1 := by sorry
        have newS : S ⊂ ↑Cantor_set:= by sorry
        apply ssubset_of_subset_of_ssubset newS Cantor_subset_Icc
      rcases xcomparez with h1 | h2
      · left
        apply h1
      · right
        apply h2
    · sorry
    · sorry
  · rcases ysmallerx with h1 | h2
    · apply nhxy
      assumption
    · sorry --/
