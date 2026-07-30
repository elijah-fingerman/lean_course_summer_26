import Mathlib.Tactic
import LectureNotes.lecture6.examples6

open MySequences

namespace MyFunctions

def continuousAt (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ y, dist y a < δ → dist (f y) (f a) < ε

def continuousOn (f : ℝ → ℝ) : Prop :=
  ∀ a, continuousAt f a

def seqContinuousAt (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x : RealSeq , tends_to x a → tends_to ⟨fun n => f (x n)⟩ (f a)

theorem continuousAt_iff_seqContinuousAt (f : ℝ → ℝ) (a : ℝ) :
  continuousAt f a ↔ seqContinuousAt f a := by
  constructor
  · intro h x hx ε hε
    obtain ⟨δ, hδ⟩ := h ε hε
    obtain ⟨N, hN⟩ := hx δ hδ.1
    use N
    intro n hn
    exact hδ.2 _ (hN n hn)
  intro hseq
  by_contra h
  unfold continuousAt at h
  push Not at h
  obtain ⟨ε, hε, h⟩ := h
  have hyn : ∀ n : ℕ, ∃ y : ℝ, dist y a < 1 / (n + 1 : ℝ) ∧ dist (f y) (f a) ≥ ε := by
    intro n
    specialize h (1 / (n + 1 : ℝ)) (by positivity) -- new! apply ∀ hypothesis to certain value
    exact h
  classical -- needed to computationally choose a sequence of y's
  choose y hy using hyn -- axiom of choice
  have hytends : tends_to ⟨y⟩ a := by
    intro ε' hε'
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε' --useful lemma to obtain N such that 1/(N+1) < ε'
    use N
    intro n hn
    have hdist := (hy n).1
    have hle : 1 / (n + 1 : ℝ) ≤ 1 / (N + 1 : ℝ) := by
      refine one_div_le_one_div_of_le ?_ ?_
      · exact Nat.cast_add_one_pos N
      exact add_le_add_left (Nat.cast_le.mpr hn) 1
    linarith
  have hyf : ¬ tends_to ⟨fun n => f (y n)⟩ (f a) := by
    unfold tends_to
    push Not
    use ε
    refine ⟨hε, ?_⟩
    exact (fun N ↦ Exists.intro N ⟨le_refl N, (hy N).2⟩)
  exact hyf (hseq ⟨y⟩ hytends)


end MyFunctions

namespace MySequences

variable {S : Set ℝ} {x : RealSeq}

#check sInf S --infinimum of a set of real numbers

#check sSup S --supremum of a set of real numbers

#check Set.range x --the set of all values of a sequence, i.e. {x n | n : ℕ} = image of x.

lemma tends_to_of_bounded_increasing {x : RealSeq} (hx : ∀ n, x n ≤ x (n + 1))
  (hbdd : ∃ M, ∀ y ∈ Set.range x, y ≤ M) : tends_to x (sSup (Set.range x)) := by
  have hdist : ∀ n, dist (x n) (sSup (Set.range x)) = sSup (Set.range x) - x n := by
      intro n
      have hle : 0 ≤ sSup (Set.range x) - x n := by
        apply sub_nonneg.mpr
        exact le_csSup hbdd (Set.mem_range_self n)
      rw[dist_comm, Real.dist_eq, abs_of_nonneg hle]
  by_contra hcon
  unfold tends_to at hcon
  push Not at hcon
  obtain ⟨ε, hε, h⟩ := hcon
  have hN : ∀ n , sSup (Set.range x) - x n ≥ ε := by
    intro n
    obtain ⟨N, hN, hN2⟩ := h (n + 1)
    have hdiff : sSup (Set.range x) - x n ≥ sSup (Set.range x) - x N := by
      apply sub_le_sub_left
      apply monotone_nat_of_le_succ hx (Nat.le_of_succ_le hN)
    rw[hdist N] at hN2
    exact le_trans hN2 hdiff
  set x2 := sSup (Set.range x) - ε/2 with hx2def -- version of let with hypothesis
  have hup : x2 ∈ upperBounds (Set.range x) := by
    intro y ⟨n, hny⟩
    calc
      y ≤ sSup (Set.range x) - ε  := by
        rw[← hny]
        exact le_sub_comm.mp (hN n)
      _ = x2 - ε/2 := by
        rw[hx2def]
        group
      _ ≤ x2 := by
        exact sub_le_self _ (le_of_lt (half_pos hε))
  have hlt : x2 < sSup (Set.range x) := by
    exact sub_lt_self _ (half_pos hε)
  have sSup_le : sSup (Set.range x) ≤ x2 := by
    apply csSup_le _ hup
    exact ⟨x 0, Set.mem_range_self 0⟩
  linarith

end MySequences
