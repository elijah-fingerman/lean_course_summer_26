import LectureNotes.lecture5.examples5
import Mathlib.Data.Nat.Factorization.Basic

open MyQuotient

-- Two integers define the same class modulo `n` exactly when they have the same remainder modulo `n`.
-- Hint: use `modulo_eq_rest` from the lecture notes.
lemma exercise0 {n m1 m2 : ℤ} (hn : n ≠ 0) : (q n m1) = q n m2 ↔ (m1 % n = m2 % n) := by
  constructor
  · intro hq
    obtain ⟨k, hk⟩ := q_equality.mp hq
    apply modulo_eq_rest n m1
      (k + m2 / n) (m2 % n) hn (⟨Int.emod_nonneg m2 hn, Int.emod_lt m2 hn⟩)
    calc
        m1 = n * k + m2 := by omega
        _ = n * k + (n * (m2 / n) + m2 % n) := by simp only [Int.mul_ediv_add_emod m2 n]
        _ = n * (k + m2 / n) + m2 % n := by ring
  · intro hmod
    apply q_equality.mpr
    use m1 / n - m2 / n
    calc
      m1 - m2 =
          (n * (m1 / n) + m1 % n) - (n * (m2 / n) + m2 % n) := by
            rw [Int.mul_ediv_add_emod, Int.mul_ediv_add_emod]
      _ = n * (m1 / n - m2 / n) := by rw [hmod]; group

/- Look at exercise_class.lean in LectureNotes/lecture4 for the setbuilder notation.
Use the properties of equivalence relations to prove the following lemma.
You can access them with `hR.refl`, `hR.symm` and `hR.trans`.
-/
lemma exercise1 {α : Type} {R : α → α → Prop} (hR : Equivalence R) (x y : α) :
    {z : α | R x z} = {z : α | R y z} ↔ R x y := by
  constructor
  · intro heq
    have hx : x ∈ {z : α | R x z} := by
      exact hR.refl x
    rw[heq] at hx
    exact hR.symm hx
  intro hRxy
  apply Set.Subset.antisymm_iff.mpr -- show both inclusions
  constructor --hint: A ⊆ B means ∀ x, x ∈ A → x ∈ B
  · intro z hz
    exact hR.trans (hR.symm hRxy) hz
  intro z hz
  exact hR.trans hRxy hz

-- use `Quotient.lift` to define a function ℤ/n → ℤ/n sending ⟦x⟧ → ⟦k * x⟧.
def mul_k (n k : ℤ) : ℤ_mod n → ℤ_mod n :=
  Quotient.lift (fun x => q n (k * x)) <| by
  intro a b h
  simp only [ℤ_mod, ℤ_mod_setoid, q]
  apply Quotient.eq.mpr
  change n ∣ (k * a) - (k * b)
  obtain ⟨l, hl⟩ := h
  use k * l
  rw[← mul_assoc, mul_comm n k, mul_assoc, ← hl]
  group


-- A function with a left inverse is injective. Only use definitions to solve this.
lemma f_injective_of_left_inverse {α β : Type} (f : α → β) (g : β → α) (h : ∀ x, g (f x) = x) :
    Function.Injective f := by
  intro x y hxy
  rw[← h x,← h y, hxy]

-- A function with a right inverse is surjective. Only use definitions to solve this.
lemma f_surjective_of_right_inverse {α β : Type} (f : α → β) (g : β → α) (h : ∀ y, f (g y) = y) :
    Function.Surjective f := by
  intro y
  use g y
  exact h y

-- Prove that the quotient map q : ℤ → ℤ/n is restricted to Fin n = {0, 1, …, n-1} is a bijection.
-- Hint: You can prove this directly.
theorem exercise2 {n : ℤ} (hn : n ≠ 0) : Function.Bijective (q_res n) := by
  constructor
  · intro x y hxy
    have hdvd : n ∣ (x : ℤ) - (y : ℤ) := Quotient.exact hxy
    have habs : ((x : ℤ) - (y : ℤ)).natAbs < n.natAbs := by
      omega
    have h0 : ((x : ℤ) - (y : ℤ)).natAbs = 0 := by
      exact Nat.eq_zero_of_dvd_of_lt (Int.natAbs_dvd_natAbs.mpr hdvd) habs
    omega
  · intro x
    obtain ⟨m, hm⟩ := Quotient.exists_rep x
    have hr0 : 0 ≤ m % n := Int.emod_nonneg m hn
    have hrlt : m % n < (n.natAbs : ℤ) := Int.emod_lt m hn
    have hfin : (m % n).toNat < n.natAbs := by
      omega
    use ⟨(m % n).toNat, hfin⟩
    rw [← hm]
    apply Quotient.eq.mpr
    change n ∣ ((m % n).toNat : ℤ) - m
    rw [Int.toNat_of_nonneg hr0]
    exact Int.dvd_emod_sub_self

-- If coprime integers `a` and `b` both divide `c`, then their product also divides `c`.
-- Hint: Start with the case of prime powers and then use the prime factorization from last time.
lemma prime_power_case {p k b c : ℕ} (hp : Nat.Prime p)
    (h1 : p ^ k ∣ c) (h2 : b ∣ c) (h3 : Nat.gcd (p ^ k) b = 1) :
    p ^ k * b ∣ c := by
  obtain ⟨l,hl⟩ := h2
  rw[hl, mul_comm]
  rw[hl] at h1
  apply Nat.mul_dvd_mul (Nat.dvd_refl b)
  cases k with
  | zero =>
    rw [pow_zero]
    exact one_dvd l
  | succ k =>
    refine (Nat.prime_iff.mp hp).pow_dvd_of_dvd_mul_left (k + 1) ?_ h1
    apply hp.coprime_iff_not_dvd.mp
    exact Nat.Coprime.of_dvd_left (dvd_pow_self p (Nat.succ_ne_zero k)) h3


lemma exercise3 {a b c : ℕ} (h1 : a ∣ c) (h2 : b ∣ c) (h3 : Nat.gcd a b = 1) : a * b ∣ c := by
  induction a using Nat.strong_induction_on generalizing b c with
  | h a ih =>
      by_cases ha0 : a = 0
      · simpa [ha0] using h1
      by_cases ha1 : a = 1
      · simpa [ha1] using h2
      obtain ⟨p, hp, hpa⟩ := Nat.exists_prime_and_dvd ha1
      let k := a.factorization p
      let r := a / p ^ k
      have hprod : p ^ k * r = a := Nat.ordProj_mul_ordCompl_eq_self a p
      have hr_dvd_a : r ∣ a := by
        use p ^ k
        rw [mul_comm]
        exact hprod.symm
      rw[← hprod, mul_assoc]
      refine prime_power_case hp ?_ ?_ ?_
      · rw[← hprod] at h1
        exact dvd_of_mul_right_dvd h1
      · refine ih r ?_ ?_ h2 (Nat.Coprime.coprime_dvd_left hr_dvd_a h3)
        · apply Nat.div_lt_self (Nat.zero_lt_of_ne_zero ha0)
          refine Nat.one_lt_pow ?_ (Nat.Prime.one_lt hp)
          exact Nat.ne_zero_of_lt (hp.factorization_pos_of_dvd ha0 hpa)
        rw[← hprod] at h1
        exact dvd_of_mul_left_dvd h1
      apply Nat.Coprime.pow_left k
      refine Nat.Coprime.mul_right ?_ ?_
      · exact Nat.coprime_ordCompl hp ha0
      exact Nat.Coprime.coprime_dvd_left hpa h3
