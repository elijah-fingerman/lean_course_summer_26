import LectureNotes.lecture6.examples6

open MySequences


/-
Hint: Use the above fact about the ceiling of a real number to find a rational number between 0 and ε.
Find a useful theorem below.
-/

example (x : ℝ) : ⌈x⌉ ≥ x := by exact Int.le_ceil x

#check one_div_le

theorem exercise1 {ε : ℝ} (hε : ε > 0) : ∃ δ : ℕ , δ > 0 ∧ (1 / δ) ≤ ε := by
  rcases exists_nat_one_div_lt hε with ⟨n, hn⟩
  refine ⟨n + 1, Nat.zero_lt_succ n, le_of_lt ?_⟩
  rw [Nat.cast_add, Nat.cast_one]
  exact hn

/-
Show that convergence can be expressed in terms of rational numbers. Use the above exercise.
-/
theorem exericse2 {x : RealSeq} (a : ℝ) (hx : ∀ δ : ℕ, δ > 0 → ∃ N, ∀ n≥ N, dist (x n) a < 1 / δ)
  : tends_toReal x a := by
  intro ε hε
  rcases exercise1 hε with ⟨δ, hδ0, hδε⟩
  rcases (hx δ hδ0) with ⟨N, hN⟩
  exact ⟨N, fun n hn => (hN n hn).trans_le hδε⟩

/-
Show that rational Cauchy sequences are also Cauchy sequences of real numbers and vice versa.
Hint below:
-/
#check Rat.dist_cast

theorem exercise3 {x : RatSeq} : isCauchy x ↔ isCauchyReal x := by
  rfl

/-
Finally, show that convergent sequences are Cauchy sequences.
-/
theorem exercise4 {x : RealSeq} (a : ℝ) (hx : tends_toReal x a) : isCauchyReal x := by
  intro ε hε
  rcases hx (ε/2) (half_pos hε) with ⟨N, hN⟩
  refine ⟨N, fun m hm n hn =>
    lt_of_le_of_lt ?_ (add_halves ε ▸ add_lt_add (hN m hm) (hN n hn))⟩
  exact (dist_comm (x.x n) a) ▸ dist_triangle _ _ _

/-
Finally, define a sequence of real numbers that does not converge.
-/

def my_diverging_sequence : RealSeq where
  x n := n

theorem exercise5 : ¬ ∃ a : ℝ, tends_toReal my_diverging_sequence a := by
  push Not
  intro a
  refine (exercise4 a).mt ?_
  unfold isCauchyReal
  push Not
  refine ⟨1/2, one_half_pos, fun N =>
    ⟨N, le_refl N, N + 1, le_add_of_nonneg_right zero_le_one, ?_⟩⟩
  unfold my_diverging_sequence
  rw [Nat.dist_cast_real, Nat.dist_eq, Nat.cast_add,
    Nat.cast_one, sub_add_cancel_left, abs_neg, abs_one]
  exact half_le_self zero_le_one
