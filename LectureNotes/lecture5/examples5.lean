import Mathlib.Tactic
import Mathlib.Data.Int.DivMod

#check ℤ

/-
Modulo calculations for integers
-/

lemma modulo_eq_rest (n m k r : ℤ) (hn : n ≠ 0) (hr : 0 ≤ r ∧ r < n.natAbs) (h : m = n * k + r)
  : m % n = r := by
  apply (Int.emod_eq_iff hn).mpr
  refine ⟨hr.1, hr.2, ?_⟩
  simp only [h, sub_add_cancel_right, dvd_neg, dvd_mul_right]

namespace MyQuotient

@[simp]
def mod_relation (n : ℤ) : ℤ → ℤ → Prop := fun m1 m2 => n ∣ m1 - m2

scoped notation m1 " ∼[" n "] " m2 => mod_relation n m1 m2

example (n m1 m2 : ℤ) : (m1 ∼[n] m2) ↔ n ∣ m1 - m2 := by
  rfl

/-
Equivalence relations are defined in the library. We prove that mod_relation n is an equivalence.
-/

#check Equivalence

@[simp]
theorem mod_equivalence (n : ℤ) : Equivalence (mod_relation n) where
  refl := by
    intro m
    simp only [mod_relation, sub_self, dvd_zero]
  symm := by
    intro m1 m2 h
    simp only [mod_relation] at *
    exact dvd_sub_comm.mp h
  trans := by
    intro m1 m2 m3 h12 h23
    simp only [mod_relation] at *
    have hdiv : m1 - m3 = (m1 - m2) + (m2 - m3) := by
      exact Eq.symm (sub_add_sub_cancel m1 m2 m3)
    rw[hdiv]
    exact (Int.dvd_add_right h12).mpr h23

/-
Equivalences and their quotients are already implemented in lean!
-/
@[simp]
def ℤ_mod_setoid (n : ℤ) : Setoid ℤ where
  r := mod_relation n
  iseqv := mod_equivalence n

@[simp]
def ℤ_mod (n : ℤ) : Type := Quotient (ℤ_mod_setoid n)

/-
The equivalence class of an integer `m` modulo `n` is denoted by `Quotient.mk (ℤ_mod_setoid hn) m`.
The quotient type is denoted by `ℤ_mod n`.
-/

example (n m : ℤ) : (ℤ_mod n) := Quotient.mk (ℤ_mod_setoid n) m

--alternatively, you can write the equivalence class using ⟦ ⟧.
example (n m : ℤ) : Quotient.mk (ℤ_mod_setoid n) m = (⟦m⟧ : ℤ_mod n) := by rfl


@[simp]
def q (n : ℤ) : ℤ → ℤ_mod n := Quotient.mk (ℤ_mod_setoid n)

lemma q_equality {n m1 m2 : ℤ} : (q n m1) = q n m2 ↔ (m1 ∼[n] m2) := by
  simp only [q, ℤ_mod_setoid, mod_relation]
  exact Quotient.eq

/-
Now we need to define the function C : ℤ_mod (n * m) → ℤ_mod n × ℤ_mod m.
We will define it in two steps, first we define the components of C : ℤ_mod (n * m) → ℤ_mod n
(respectively → ℤ_mod m) and then we define the function C : ℤ_mod (n * m) → ℤ_mod n × ℤ_mod m.
Rememeber components ℤ_mod (n * m) → ℤ_mod n were given by [x]_nm ↦ ([x]_n), respectively,
ℤ_mod (n * m) → ℤ_mod m, [x]_nm ↦ ([x]_m).
For this we will use the Quotient lift property.
-/

#check Quotient.lift

def C_dvd {n1 n2 : ℤ} (hdvd : n1 ∣ n2) : ℤ_mod (n2) → ℤ_mod n1 := by
  refine Quotient.lift (fun m => q n1 m) ?_
  intro m1 m2 h
  simp only [q_equality, mod_relation] at *
  exact dvd_trans hdvd h

def C (n m : ℤ) : ℤ_mod (n * m) → ℤ_mod n × ℤ_mod m := by
  intro x
  exact ⟨(C_dvd (Int.dvd_mul_right n m)) x, C_dvd (Int.dvd_mul_left n m) x⟩


theorem chinese_remainder_theorem' {n m : ℤ} (hn : n ≠ 0) (hm : m ≠ 0) (hcoprime : Int.gcd n m = 1) :
    Function.Bijective (C n m) := by
  sorry

/-
Interlude: Functions
-/

section

variable {α β : Type} (f : α → β)

#check Function.Injective f

#check Function.Surjective f

#check Function.Bijective f

#check α ≃ β -- the type of equivalences (bijective functions) between α and β

noncomputable example (h : Function.Bijective f) : α ≃ β  := by
  exact Equiv.ofBijective f h

variable {e : α ≃ β}

#check e.toFun --function from α to β

#check e.invFun --inverse function from β to α

#check e.symm --equivalence from β to α (given by the inverse function)

-- Finite sets have a cardinality, which is a natural number.

#check Finite α -- Finite a means α is equivalent to Fin n for some n : ℕ.

#check Nat.card -- Nat.card α is the cardinality of a finite type α.

lemma bijective_of_injective_and_card {α β : Type} [Finite α] [Finite β] (f : α → β)
    (h : Function.Injective f) (hcard : Nat.card α = Nat.card β) : Function.Bijective f := by
  exact (Nat.bijective_iff_injective_and_card f).mpr ⟨h, hcard⟩

end

def q_res (n : ℤ) : Fin n.natAbs → ℤ_mod n := fun i => q n i.val

theorem Z_mod_n_fin_n_bijection {n : ℤ} (hn : n ≠ 0) : Function.Bijective (q_res n) := by
  refine ⟨?_, ?_⟩
  · sorry
  sorry

noncomputable def Z_mod_n_fin_n_equiv {n : ℤ} (hn : n ≠ 0) : ℤ_mod n ≃ Fin n.natAbs:= by
  exact (Equiv.ofBijective (q_res n) (Z_mod_n_fin_n_bijection hn)).symm

theorem finiteness_of_Z_mod {n : ℤ} (hn : n ≠ 0) : Finite (ℤ_mod n) := by
  apply finite_iff_exists_equiv_fin.mpr
  use n.natAbs
  exact ⟨Z_mod_n_fin_n_equiv hn⟩

theorem chinese_remainder_theorem {n m : ℤ} (hn : n ≠ 0) (hm : m ≠ 0) (hcoprime : IsCoprime n m) :
    Function.Bijective (C n m) := by
  refine @bijective_of_injective_and_card _ _ ?_ ?_ (C n m) ?_ ?_
  · apply finiteness_of_Z_mod
    exact Int.mul_ne_zero hn hm
  · refine (@Prod.finite_iff _ _ ?_ ?_).mpr ?_
    · exact ⟨(q n 0)⟩
    · exact ⟨(q m 0)⟩
    exact ⟨finiteness_of_Z_mod hn, finiteness_of_Z_mod hm⟩
  · intro m1 m2 h
    obtain ⟨x1, h1⟩ := Quotient.exists_rep m1
    obtain ⟨x2, h2⟩ := Quotient.exists_rep m2
    rw[← h1,← h2]
    apply Quotient.eq.mpr
    change n * m ∣ (x1 - x2)
    have hCx1 : (C_dvd (Int.dvd_mul_right n m) m1, C_dvd (Int.dvd_mul_left n m) m1)
    = (q n x1, q m x1) := by
      rw [← h1]
      rfl
    have hCx2 : (C_dvd (Int.dvd_mul_right n m) m2, C_dvd (Int.dvd_mul_left n m) m2)
    = (q n x2, q m x2) := by
      rw [← h2]
      rfl
    simp only [C, hCx1, hCx2] at h
    have hndvd : n ∣ (x1 - x2) := by
      change x1 ∼[n] x2
      exact q_equality.mp (congrArg Prod.fst h)
    have hmdvd : m ∣ (x1 - x2) := by
      change x1 ∼[m] x2
      exact q_equality.mp (congrArg Prod.snd h)
    exact IsCoprime.mul_dvd hcoprime hndvd hmdvd
  have hnmcard : Nat.card (ℤ_mod (n * m)) = (n * m).natAbs := by
    exact Nat.card_eq_of_equiv_fin (Z_mod_n_fin_n_equiv (Int.mul_ne_zero hn hm))
  have hprodcard : Nat.card (ℤ_mod n × ℤ_mod m) = n.natAbs * m.natAbs := by
    rw[Nat.card_prod]
    rw[(Nat.card_eq_of_equiv_fin (Z_mod_n_fin_n_equiv hn)),
    (Nat.card_eq_of_equiv_fin (Z_mod_n_fin_n_equiv hm))]
  rw[hnmcard, hprodcard]
  exact Int.natAbs_mul n m

end MyQuotient
