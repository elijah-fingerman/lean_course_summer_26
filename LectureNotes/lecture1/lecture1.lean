import VersoSlides
import Verso.Doc.Concrete

open VersoSlides

set_option verso.code.warnLineLength 100
set_option verso.slides.panel false

#doc (Slides) "Mathematics in Lean - Lecture 1" =>

# Mathematics in Lean

%%%
backgroundGradient := some "linear-gradient(135deg, #172554 0%, #1e3a8a 52%, #0f766e 100%)"
%%%

:::class "title-kicker"
LECTURE 1
:::

:::fitText
When is a mathematical statement true?
:::

From proofs on paper to proofs checked by a computer.

# What is a mathematical statement?

Mathematics is always formulated in the context of a theory. A theory consists of

:::::::hstack
:::::class "text-box"
:::fragment fadeUp
Basic objects and definitions
:::
:::::

:::::class "text-box"
:::fragment fadeUp
A set of axioms
:::
:::::

:::::class "text-box"
:::fragment fadeUp
Rules of inference
:::
:::::
:::::::


# The natural numbers

:::::::hstack
:::::class "text-box"
:::fragment fadeUp
Positive integers
:::
:::::

:::::class "text-box"
:::fragment fadeUp
Successor, Addition, Multiplication
:::
:::::

:::::class "text-box"
:::fragment fadeUp
Peano Axioms
:::
:::::
:::::::

:::fragment fadeUp
$$`\textbf{Proposition.}\quad \text{For every natural number } n,\; n + 0 = 0 + n \text{ holds.}`
:::

:::::fragment fadeUp
:::class "emphasis-box"
What makes this statment true?
:::
:::::

# A proof!

A formal proof is a sequence of steps, where each step is either

:::fragment fadeUp
* An axiom
:::

:::fragment fadeUp
* A known statement
:::

:::fragment fadeUp
* The result of applying an inference rule to earlier lines
:::

:::::fragment fadeUp
:::class "emphasis-box"
Goal of the course: Use a computer program to verify mathematical proofs.
:::
:::::


# Propositions

:::fragment fadeUp
A proposition is a statement within a theory. A proposition can either have a formal proof or not. If it has a proof, we say the proposition is _true_ or _provable_.
:::

:::fragment fadeUp
A proposition consists of
:::
:::fragment fadeUp
* Variables, which are the objects of the theory, $`x, y, z, \dots`
:::
:::fragment fadeUp
* Predicates, which are functions from objects to propositions, $`P(x), Q(y)`
:::
:::fragment fadeUp
* Quantifiers $`\forall` and $`\exists`
:::
:::fragment fadeUp
* Logical connectives, which combine propositions into new propositions, $`\wedge, \vee, \to, \neg`
:::
:::fragment fadeUp
* Constants, which are propositions that are by definition provable or not provable, $`\top, \bot`
:::


# Propositions continued

:::fragment fadeUp
Let A, B be two propositions. Then
:::

:::fragment fadeUp
* $`A \wedge B` is provable if and only if both A and B are provable.
:::
:::fragment fadeUp
* $`A \vee B` is provable if and only if at least one of A or B is provable.
:::
:::fragment fadeUp
* $`A \to B` is provable if and only if whenever A is provable, B is provable.
:::
:::fragment fadeUp
* $`\neg A` is defined as $`A \to \bot`, i.e. $`\neg A` is provable if and only if a proof of A leads to a contradiction.
:::

# Back to the natural numbers

The natural numbers are built from the following operations:
* $`0` is a natural number;
* Every natural number $`n` has a successor $`S(n)`.
* Every two natural numbers can be added and multiplied together.

:::::::::fragment fadeUp
These operations follow the following axioms, called the Peano axioms:

:::::class "axiom-grid"
:::vstack
(1) $`∀ n, 0 ≠ S(n)`

(2) $`S(n) = S(m) → n = m`

(3) $`\forall n, n + 0 = n`

(4) $`\forall n ∀ m, n + S(m) = S(n + m)`

(5) $`\forall n, n * 0 = 0`

(6) $`\forall n ∀ m, n * S(m) = n * m + n`
:::
:::::
:::::::::

::::::fragment fadeUp
:::class "emphasis-box"
(7) $`P(0) \wedge (\forall n, P(n) \to P(S(n))) \to \forall n, P(n)`
:::
::::::

# Example 1

$`\textbf{Proposition 1.}\quad P(n) = n * S(0)= n`.

Proof:
:::fragment fadeUp
* Axiom 6 gives $`n * S(0) = n * 0 + n`
:::
:::fragment fadeUp
* Axiom 5 gives $`n * 0 = 0`
:::
:::fragment fadeUp
* By substitution $`n * S(0) = 0 + n`
:::
:::fragment fadeUp
* Remains to show $`0 + n = n`.
:::

# Example 2
$`\textbf{Proposition 2.}\quad Q(n) = 0 + n= n`.

Proof:
:::fragment fadeUp
Proof by induction (Axiom 7).
:::
:::fragment fadeUp
* Q(0) = $`0 + 0 = 0` is true by axiom 3.
:::
:::fragment fadeUp
Need to show $`Q(n) \to Q(S(n))`.
:::
:::fragment fadeUp
* Assume Q(n), i.e., $`0 + n = n` holds.
:::
:::fragment fadeUp
* Want to show $`Q(S(n)) := 0 + S(n) = S(n)`.
:::
:::fragment fadeUp
* Axiom 4 gives $`0 + S(n) = S(0 + n)`.
:::
:::fragment fadeUp
* $`S(0 + n) = S(n)` by Q(n).
:::

# Example 3
$`\textbf{Proposition 3.}\quad R(n) = ∀ m, n + m = m + n`.

Proof:
:::fragment fadeUp
Proof by induction (Axiom 7).
:::
:::fragment fadeUp
* Base case: $`R(0) = \forall m, 0 + m = m + 0`, both sides are equal to m by axioms 3 and Example 2.
:::
:::fragment fadeUp
* Induction step: Assume R(n), i.e. $`n + m = m + n` for all m. Need to show $`R(S(n)) = S(n) + m = m + S(n)` for all m.
:::
:::fragment fadeUp
* Axiom 4 gives $`S(n) + m = S(n + m)`.
:::
:::fragment fadeUp
* By the induction hypothesis, $`S(n + m) = S(m + n)`.
:::
:::fragment fadeUp
* Axiom 4 gives $`S(m + n) = m + S(n)`
:::
:::fragment fadeUp
* Therefore $`S(n) + m = m + S(n)` for all m.
:::
