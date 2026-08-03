import LectureNotes.lecture7.examples7

open MyFunctions MySequences

namespace MySequences

/-!
## Lemmas for sequences
-/

/-- The sum of two convergent sequences converges to the sum of their limits. -/
lemma tends_to_add {x y : RealSeq} {a b : ℝ}
    (hx : tends_to x a) (hy : tends_to y b) :
    tends_to ⟨fun n ↦ x n + y n⟩ (a + b) := by
  intro ε hε
  have ⟨N, hN⟩ := hx (ε / 2) (half_pos hε)
  have ⟨M, hM⟩ := hy (ε / 2) (half_pos hε)
  exact ⟨max N M, fun N' hN' => add_halves ε ▸
    lt_of_le_of_lt (dist_add_add_le (x.x N') (y.x N') a b) (add_lt_add
    (hN N' ((le_max_left _ _).trans hN')) (hM N' ((le_max_right _ _).trans hN')))⟩

-- For exercise 2
lemma tends_to_le_of_le {x : RealSeq} {a b : ℝ} (hx : tends_to x a) (h : ∀ n, x n ≤ b) :
    a ≤ b := by
  by_contra hab
  have ⟨N, hN⟩ := hx (a - b) (sub_pos.mpr (not_le.mp hab))
  exact not_lt_of_ge (h N) (sub_sub_cancel a b ▸
    (sub_lt_of_abs_sub_lt_left ∘ hN N) le_rfl)

-- For exercise 2
lemma tends_to_ge_of_ge {x : RealSeq} {a b : ℝ} (hx : tends_to x a) (h : ∀ n, x n ≥ b) :
    a ≥ b := by
  by_contra hab
  have ⟨N, hN⟩ := hx (b - a) (sub_pos.mpr (not_le.mp hab))
  exact not_lt_of_ge (h N) (sub_add_cancel b a ▸ add_comm a _ ▸
    (sub_lt_iff_lt_add).mp ((sub_lt_of_abs_sub_lt_right ∘ hN N) le_rfl))

end MySequences

/-!
## Exercise 1: continuous functions
-/
namespace MyFunctions

/-
Use `continuousAt_iff_seqContinuousAt` for the exercise.
You may find `Function.comp_apply` useful when simplifying compositions.
-/
lemma continuous_comp_of_continuous {f g : ℝ → ℝ} {a : ℝ}
    (hf : continuousAt f a) (hg : continuousAt g (f a)) :
    continuousAt (g ∘ f) a := by
  rw [continuousAt_iff_seqContinuousAt] at *
  exact fun r hr => hg ⟨(fun n => f (r n))⟩ (hf r hr)

/-
Use the above lemma to prove that the sum of two continuous functions is continuous.
-/
lemma continuous_sum_of_continuous {f g : ℝ → ℝ} {a : ℝ}
    (hf : continuousAt f a) (hg : continuousAt g a) :
    continuousAt (f + g) a := by
  rw [continuousAt_iff_seqContinuousAt] at *
  exact fun r hr => tends_to_add (hf r hr) (hg r hr)

end MyFunctions

/-!
## Exercise 2: the least-upper-bound property
-/

/-
Do not use `sSup`, `le_csSup`, or `csSup_le` in this exercise. The aim is to
derive the least-upper-bound property from Cauchy completeness.

Use a bisection construction:

1) Choose `l₀ ∈ S` using `hS`, and choose an upper bound `u₀` using `hbdd`.
   Thus `l₀ ≤ u₀`.

2) Recursively bisect the interval `[lₙ, uₙ]`. Let
   `mₙ = (lₙ + uₙ) / 2`.

   * If `mₙ ∈ upperBounds S`, set `lₙ₊₁ = lₙ` and `uₙ₊₁ = mₙ`.
   * Otherwise, there is some `y ∈ S` with `mₙ < y`. Choose such a `y`,
     set `lₙ₊₁ = y`, and keep `uₙ₊₁ = uₙ`.

   You'll need `classical` to make these choices.

3) Prove by induction that:

   * `lₙ ∈ S`;
   * `uₙ ∈ upperBounds S`;
   * the intervals are nested; and
   * `uₙ - lₙ ≤ (u₀ - l₀) / 2^n`.

4) Deduce that `⟨l⟩ : RealSeq` is Cauchy. For sufficiently large `N`,
   every `lₙ` with `n ≥ N` lies in `[l_N, u_N]`, whose length tends to
   zero. The lemmas `exists_pow_lt_of_lt_one` and `one_half_lt_one` may
   help with the powers of `1 / 2`.

5) Apply `MySequences.real_numbers_complete` from last time to obtain a real number `a` to which
   `l` converges. This `a` will be the supremum; do not identify it with
   the library term `sSup S`.

6) Use the two lemmas above about limits to show that `a` satisfied the least-upper-bound property.
Hint: a is also the limit of the sequence `u`.

7) Prove the at least one of the lemmas about limits above.
-/

lemma exercise2 {S : Set ℝ} (hS : S.Nonempty) (u : upperBounds S) :
    ∃ sup : upperBounds S, ∀ b : upperBounds S, sup ≤ b := by
  /-
  heavily referenced existing solution, with the intent of
  understanding how it translated things to Lean, and seeing if
  any areas could be improved; currently unfinished
  -/

  classical
  have ⟨l₀, hl₀⟩ := hS
  have ⟨u₀, hu₀⟩ := u
  let A := {c : ℝ × ℝ // c.1 ∈ S ∧ c.2 ∈ upperBounds S}
  let bisect : A -> A := fun a => (
    if ha : (a.1.1 + a.1.2) / 2 ∈ upperBounds S then
      ⟨⟨a.1.1, (a.1.1 + a.1.2) / 2⟩, a.2.1, ha⟩
    else
      let h := not_forall.mp (mem_upperBounds.mpr.mt ha)
      let r : S := ⟨h.choose, by
        by_contra hnS
        exact h.choose_spec fun hS => (hnS hS).elim⟩
      ⟨⟨r, a.1.2⟩, r.2, a.2.2⟩
  )
  let c : ℕ -> A := (Nat.rec ⟨⟨l₀, u₀⟩, hl₀, hu₀⟩ (fun _ cn => bisect cn) ·)
  let l : ℕ -> ℝ := fun n => (c n).1.1
  let u : ℕ -> ℝ := fun n => (c n).1.2
  have hlS (n : ℕ) : l n ∈ S := (c n).2.1
  have hub (n : ℕ) : u n ∈ upperBounds S := (c n).2.2
  have hnest (n : ℕ) : l n ≤ u n ∧ l n ≤ l (n + 1) ∧ u n ≥ u (n + 1) := by
    refine ⟨hub n (hlS n), ?_⟩
    sorry
  have hlu_step (n : ℕ) : u (n + 1) - l (n + 1) ≤ (u n - l n) / 2 := by
    sorry
  have hlu (n : ℕ) : u n - l n ≤ (u₀ - l₀) / 2^n := by
    induction n with
    | zero =>
      simp only [Nat.rec_zero, pow_zero, div_one, tsub_le_iff_right, u, c]
      exact le_tsub_add
    | succ n hn =>
      rw [pow_succ, ←div_div]
      exact le_trans (hlu_step n) (div_le_div_of_nonneg_right hn zero_le_two)
  have hNε (ε : ℝ) (hε : ε > 0) : ∃ N, (u₀ - l₀) / 2 ^ N < ε := by
    by_cases h : u₀ = l₀
    · use 0
      rw [h, sub_self, pow_zero, div_one]
      exact hε
    · have hul0 := (sub_pos.mpr (lt_of_le_of_ne (hu₀ hl₀) (Ne.symm h)))
      have ⟨N, hN⟩ := exists_pow_lt_of_lt_one
        (x := ε / (u₀ - l₀)) (y := 1/2)
        (div_pos hε hul0) one_half_lt_one
      use N
      rw [div_eq_mul_inv, mul_comm]
      rw [one_div, inv_pow] at hN
      exact (div_mul_cancel₀ ε (ne_of_gt hul0)) ▸ mul_lt_mul_of_pos_right hN hul0
  have h_cauchy : isCauchyReal ⟨l⟩ := by
    intro ε hε
    have ⟨N, hN⟩ := hNε ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    change |l m - l n| < ε
    sorry
  have ⟨a, ha⟩ := real_numbers_complete h_cauchy
  simp only [Subtype.forall, Subtype.exists, Subtype.mk_le_mk, exists_prop]
  have htend0 : tends_to ⟨fun n => u n - l n⟩ 0 := by
    intro ε hε
    have ⟨N, hN⟩ := hNε ε hε
    refine ⟨N, fun N' hN' => ?_⟩
    rw [dist_zero_right, Real.norm_eq_abs]
    change |u N' - l N'| < ε
    sorry
  refine ⟨a, ?_, fun b hb => tends_to_le_of_le ha (fun n => hb (hlS n))⟩
  intro r hr
  sorry

/-
Bonus! think about how to prove that every real number has a decimal expansion.
Hint: Use the floor function and look at `Σ'` and `HasSum`.
-/