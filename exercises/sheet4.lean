import lecture5.examples5

open MyQuotient

-- Two integers define the same class modulo `n` exactly when they have the same remainder modulo `n`.
-- Hint: use `modulo_eq_rest` from the lecture notes.
lemma exercise0 {n m1 m2 : ℤ} (hn : n ≠ 0) : (q n m1) = q n m2 ↔ (m1 % n = m2 % n) := by
  constructor
  · intro hq
    exact (Int.modEq_iff_dvd.mpr (Quotient.exact hq)).symm
  · intro hm
    exact q_equality.mpr (Int.modEq_iff_dvd.mp hm.symm)

/- Look at exercise_class.lean in lecture-notes/lecture4 for the setbuilder notation.
Use the properties of equivalence relations to prove the following lemma.
You can access them with `hR.refl`, `hR.symm` and `hR.trans`.
-/
lemma exercise1 {α : Type} {R : α → α → Prop} (hR : Equivalence R) (x y : α) :
    {z : α | R x z} = {z : α | R y z} ↔ R x y := by
  constructor
  · intro hzxy
    exact (Set.ext_iff.mp hzxy y).mpr (hR.refl y)
  · intro hRxy
    apply Set.Subset.antisymm_iff.mpr
    constructor <;> intro a
    · exact hR.trans (hR.symm hRxy)
    · exact hR.trans hRxy

-- use `Quotient.lift` to define a function ℤ/n → ℤ/n sending ⟦x⟧ → ⟦k * x⟧.
def mul_k (n k : ℤ) : ℤ_mod n → ℤ_mod n := by
  refine Quotient.lift (q n ∘ (k * ·)) ?_
  rintro a b ⟨j, hj⟩
  refine Quotient.eq_iff_equiv.mpr ⟨k * j, ?_⟩
  rw [← mul_sub, mul_left_comm, hj]

-- A function with a left inverse is injective. Only use definitions to solve this.
lemma f_injective_of_left_inverse {α β : Type} (f : α → β) (g : β → α) (h : ∀ x, g (f x) = x) :
    Function.Injective f := by
  exact fun a b h' => (h a ▸ h b ▸ congrArg g h')

-- A function with a right inverse is surjective. Only use definitions to solve this.
lemma f_surjective_of_right_inverse {α β : Type} (f : α → β) (g : β → α) (h : ∀ y, f (g y) = y) :
    Function.Surjective f := by
  exact fun b => ⟨g b, h b⟩

-- Prove that the quotient map q : ℤ → ℤ/n is restricted to Fin n = {0, 1, …, n-1} is a bijection.
-- Hint: You can prove this directly.
theorem exercise2 {n : ℤ} (hn : n ≠ 0) : Function.Bijective (q_res n) := by
  refine ⟨?_, ?_⟩
  · intro a b h
    rcases q_equality.mp h with ⟨k, hk⟩
    have hnab : -(n.natAbs : ℤ) < a - b ∧ a - (b : ℤ) < n.natAbs := by
      constructor
      · rw [sub_eq_add_neg]
        refine lt_of_lt_of_le
          (neg_lt_neg_iff.mpr (Int.ofNat_lt.mpr b.isLt)) ?_
        nth_rw 1 [← zero_add (-(b : ℤ))]
        exact add_le_add_left (Int.natCast_nonneg ↑a) (- (b.val : ℤ))
      · rw [sub_lt_iff_lt_add]
        exact lt_of_lt_of_le (Int.ofNat_lt.mpr a.isLt)
          (le_add_of_nonneg_right (Int.natCast_nonneg ↑b))
    have hk0 : k = 0 := by
      by_contra hk0
      have hnk : (n.natAbs : ℤ) ≤ |n * k| := by
        nth_rw 1 [abs_mul, Int.abs_eq_natAbs, ← mul_one (n.natAbs : ℤ)]
        exact mul_le_mul_of_nonneg_left (Int.one_le_abs hk0)
          (le_of_lt (Int.ofNat_lt.mpr (Int.natAbs_pos.mpr hn)))
      exact (not_lt_of_ge hnk) (hk ▸ (abs_lt).2 hnab)
    rw [hk0, mul_zero, sub_eq_zero] at hk
    exact Fin.eq_of_val_eq (Int.ofNat_inj.mp hk)
  · intro qn
    rcases qn.exists_rep with ⟨a, rfl⟩
    letI : NeZero n.natAbs := ⟨Int.natAbs_ne_zero.mpr hn⟩
    refine ⟨Fin.ofNat n.natAbs (a % n).natAbs, ?_⟩
    apply q_equality.mpr
    change n ∣ (↑↑(Fin.ofNat n.natAbs (a % n).natAbs) : ℤ) - a
    simp only [Fin.ofNat, Int.natCast_emod, Int.natAbs_of_nonneg (Int.emod_nonneg a hn),
      Nat.cast_natAbs, Int.cast_abs, Int.cast_eq, Int.emod_abs]
    rw [← (Int.ediv_mul_add_emod a n)]
    simp only [Int.add_emod_emod, Int.mul_add_emod_self_right, dvd_refl, Int.emod_emod_of_dvd,
      sub_add_cancel_right, dvd_neg, dvd_mul_left]

-- If coprime integers `a` and `b` both divide `c`, then their product also divides `c`.
-- Hint: Start with the case of prime powers and then use the prime factorization from last time.
lemma exercise3 {a b c : ℕ} (h1 : a ∣ c) (h2 : b ∣ c) (h3 : Nat.gcd a b = 1) : a * b ∣ c := by
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd h3 h1 h2
