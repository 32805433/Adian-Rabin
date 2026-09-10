import Mathlib.Computability.RE
import Mathlib.GroupTheory.PresentedGroup

namespace Undecidability

/-- A letter in a word on `n` generators. The Boolean records the sign. -/
abbrev SignedGenerator (n : ℕ) := Fin n × Bool

/-- A word on `n` generators. -/
abbrev Word (n : ℕ) := List (SignedGenerator n)

/--
Syntax for a finite group presentation with exactly `n` generator slots and
exactly `m` relator slots.
-/
structure FP (n m : ℕ) where
  relator : Fin m → Word n

namespace FP

/-- The relators of a finite presentation, interpreted in the free group. -/
def relSet (P : FP n m) : Set (FreeGroup (Fin n)) :=
  Set.range fun i => FreeGroup.mk (P.relator i)

/-- The word problem for a finite presentation. -/
def wordProblem (P : FP n m) (w : Word n) : Prop :=
  PresentedGroup.mk P.relSet (FreeGroup.mk w) = 1

/-- A presentation presents the trivial group when every word represents `1`. -/
def presentsTrivial (P : FP n m) : Prop :=
  ∀ w : Word n, P.wordProblem w

/--
A family of finite presentations is effective when one algorithm computes the
`i`th relator of the `j`th presentation from `j` and `i`.
-/
def Effective (A : ℕ → FP n m) : Prop :=
  Computable₂ fun j i => (A j).relator i

/--
An effective Adian--Rabin family for triviality: there is no algorithm deciding
which member of the family presents the trivial group.
-/
def IsAdianRabinFamily (A : ℕ → FP n m) : Prop :=
  Effective A ∧
    ¬ ComputablePred fun j => (A j).presentsTrivial

end FP

/-- There is a three-generator, nine-relator group with unsolvable word problem. -/
theorem exists_three_generator_nine_relator_group_with_unsolvable_word_problem :
    ∃ P : FP 3 9,
      ¬ ComputablePred P.wordProblem := by
  sorry

/--
There is an effective Adian--Rabin family for triviality whose members have four
generators and eleven relators.
-/
theorem exists_four_generator_eleven_relator_adian_rabin_family :
    ∃ A : ℕ → FP 4 11,
      FP.IsAdianRabinFamily A := by
  sorry

/--
There is an effective Adian--Rabin family for triviality whose members have two
generators and ten relators.
-/
theorem exists_two_generator_ten_relator_adian_rabin_family :
    ∃ A : ℕ → FP 2 10,
      FP.IsAdianRabinFamily A := by
  sorry

end Undecidability
