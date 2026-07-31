import LectureNotes.lecture6.examples6

open MySequences


/-
Hint: Use the above fact about the ceiling of a real number to find a rational number between 0 and ε.
Find a useful theorem below.
-/

example (x : ℝ) : ⌈x⌉ ≥ x := by exact Int.le_ceil x

#check one_div_le

theorem exercise1 {ε : ℝ} (hε : ε > 0) : ∃ δ : ℕ , δ > 0 ∧ (1 / δ) ≤ ε := by
  by_cases h : ε ≤ 1
  · use ⌈1 / ε⌉.toNat
    refine ⟨Nat.ceil_pos.mpr (show 0 < ⌈1 / ε⌉ by positivity), ?_⟩
    apply (one_div_le _ _).mpr
    · have h : (⌈1 / ε⌉.toNat : ℝ) = ⌈1 / ε⌉ := by
        exact_mod_cast Int.toNat_of_nonneg (show 0 ≤ ⌈1 / ε⌉ by positivity)
      rw[h]
      exact Int.le_ceil (1 / ε)
    · refine Nat.cast_pos'.mpr ?_
      exact Nat.ceil_pos.mpr (show 0 < ⌈1 / ε⌉ by positivity)
    exact hε
  use 1
  exact ⟨by positivity, by linarith⟩

/-
Show that convergence can be expressed in terms of rational numbers. Use the above exercise.
-/
theorem exericse2 {x : RealSeq} (a : ℝ) (hx : ∀ δ : ℕ, δ > 0 → ∃ N, ∀ n≥ N, dist (x n) a < 1 / δ)
  : tends_to x a := by
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := exercise1 hε
  obtain ⟨N, hN⟩ := hx δ hδ
  use N
  intro n hn
  linarith [hN n hn]


/-
Show that rational Cauchy sequences are also Cauchy sequences of real numbers and vice versa.
Hint below:
-/
#check Rat.dist_cast

theorem exercise3 {x : RatSeq} : isCauchy x ↔ isCauchyReal x := by
  constructor
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    use N
    simp only [ge_iff_le, Rat.dist_cast]
    exact hN
  intro h ε hε
  obtain ⟨N, hN⟩ := h ε hε
  use N
  simp only [ge_iff_le, Rat.dist_cast] at hN
  exact hN

/-
Finally, show that convergent sequences are Cauchy sequences.
-/
theorem exercise4 {x : RealSeq} (a : ℝ) (hx : tends_to x a) : isCauchyReal x := by
  intro ε hε
  have hε2 : ε / 2 > 0 := by positivity
  obtain ⟨N, hN⟩ := hx (ε / 2) hε2
  use N
  intro m hm n hn
  calc _
    dist (x m) (x n) ≤ dist (x m) a + dist a (x n) := dist_triangle (x m) a (x n)
    _ = dist (x m) a + dist (x n) a := by rw[dist_comm a (x n)]
    _ < ε / 2 + ε / 2 := by exact add_lt_add (hN m hm) (hN n hn)
    _ = ε := by exact add_halves ε

/-
Finally, define a sequence of real numbers that does not converge.
-/

def my_diverging_sequence : RealSeq where
  x n := (-1 : ℝ) ^ n

theorem exercise5 : ¬ ∃ a : ℝ, tends_to my_diverging_sequence a := by
  let x := my_diverging_sequence
  intro h
  obtain ⟨a, ha⟩ := h
  have h1 := ha 1 Real.zero_lt_one
  have h2 := ha 1 Real.zero_lt_one
  obtain ⟨N, hN⟩ := h1
  obtain ⟨M, hM⟩ := h2
  let K := max N M
  have hcon :  dist (x K) (x (K+1)) = 2 := by
    calc
      dist (x K) (x (K+1)) = abs ((-1 : ℝ) ^ K - (-1 : ℝ) ^ (K + 1)) := by rfl
      _ = abs ((-1 : ℝ) ^ K * 2) := by ring_nf
      _ = 1 * 2 := by simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, Nat.abs_ofNat,
        one_mul]
      _ = 2 := by exact one_mul 2
  have hkM : K ≥ M := by exact le_max_right N M
  specialize hN K (le_max_left N M)
  specialize hM (K + 1) (by linarith)
  have hdist : dist (x K) (x (K + 1)) < 2 := by
    calc
      dist (x K) (x (K + 1)) ≤ dist (x K) a + dist a (x (K + 1)) := dist_triangle (x K) a (x (K + 1))
      _ = dist (x K) a + dist (x (K + 1)) a := by rw[dist_comm a (x (K + 1))]
      _ < 1 + 1 := by exact add_lt_add hN hM
      _ = 2 := by exact one_add_one_eq_two
  linarith
