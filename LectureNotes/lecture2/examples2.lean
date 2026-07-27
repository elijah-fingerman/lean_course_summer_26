import Std
import Mathlib.Tactic.ByContra

-- Example 1. Implication is a function

/-
The Curry-Howard correspondence says that every proposition defines a type,
and a proof of that proposition corresponds to a term of that type.
In particular, an implication P → Q is a function from the type P to the type Q.
In other words, a proof of P → Q is a function that takes a proof of P and returns a proof of Q.
-/

variable {P Q : Prop}

theorem example1 (hp : P) (h : P → Q) : Q := by
  apply h
  exact hp

theorem example1' (hp : P) (h : P → Q) : Q := by
  exact h hp

theorem example1'' (hp : P) (h : P → Q) : Q :=
  h hp

-- Example 2. AND is a product

theorem example2 (hp : P) (hq : Q) : P ∧ Q := by
  constructor
  · exact hp
  exact hq

/-
We used the 'constructor' tactic to prove a conjunction.
Whenever your goal is of the form P ∧ Q, this tactic creates two subgoals, one for each conjunct.
-/

theorem example2' (hp : P) (hq : Q) : P ∧ Q :=
  ⟨hp, hq⟩

--Alternatively, we can use the ⟨-,-⟩ notation to construct a term of the conjunction type directly.

-- Example 3. OR is a sum

theorem example3 (hp : P) : P ∨ Q := by
  left
  exact hp

theorem example3' (hq : Q) : P ∨ Q := by
  right
  exact hq

/-
Whenever your goal is of the form P ∨ Q, we can use the 'left' or 'right' tactic to tell the proof
assistant which disjunct we want to prove.
The 'left' tactic creates a subgoal for the first disjunct,
and the 'right' tactic creates a subgoal for the second disjunct.
-/

theorem example3'' (h : P ∨ Q) : Q ∨ P := by
  cases h with
  | inl hp =>
      right
      exact hp
  | inr hq =>
      left
      exact hq

-- Example 4. NOT is a function to false

theorem example4 (h1 : P → Q) (h2 : ¬ Q) : ¬ P := by
  intro hp
  have hq := h1 hp
  exact h2 hq

/-
When proving an implication, here (P → False), we can use the 'intro' tactic to introduce
the assumption of the implication into the context.
Moreover, the 'have' tactic allows us to create a new hypothesis in the context.
-/


theorem example4' (h1 : P → Q) (h2 : ¬ Q) : ¬ P :=
  fun hp => h2 (h1 hp)

/-
Alternatively, we can use the 'fun' keyword to define a function that takes the assumption of
the implication as an argument.
-/


theorem example4'' (h1 : P → Q) (h2 : ¬ Q) : ¬ P :=
  h2.comp h1

-- The composition of two functions (or implications) is written as h2.comp h1.


theorem double_negation : ¬ ¬ P ↔ P := by
  exact not_not

-- When we expect a result to be present in the library, we can use exact? to search for it.

-- Contrapostion

theorem contraposition (h : P → Q) : ¬ Q → ¬ P := by
  intro hq
  exact example4' h hq


theorem contraposition' (h : P → Q) : ¬ Q → ¬ P :=
  fun hq hp => hq (h hp)


-- Proof by contradiction

theorem excluded_middle : P ∨ ¬ P := by
  exact Classical.em P

theorem by_contradiction1 (h : ¬ P → False) : P :=
  double_negation.mp h

/-
When we have a theorem of the form P ↔ Q, we can access the individual implications
using the .mp (P → Q), and .mpr (Q → P) methods.
-/

theorem by_contradiction2 (h : ¬ P → False) : P := by
  by_contra hnp
  exact h hnp

/-
The tactic called 'by_contra' that allows us to prove a proposition by contradiction.
It changes the goal from P to False, and adds ¬ P to the context.
-/
