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
    set A : Set Cantor_set := {x | (x: ℝ) ∈ Set.Ioo 0 z}
    set B : Set Cantor_set := {x | (x: ℝ) ∈ Set.Ioo z 1}
    have hfinal_1 : IsOpen A ∧ IsOpen B ∧ Cantor_set ⊆ A ∪ B ∧ Set.Nonempty (Cantor_set ∪ A) ∧
       Set.Nonempty (Cantor_set ∪ B) := by sorry
    have bla : ¬ Set.Nonempty (S ∩ (A ∩ B)) := by sorry
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
