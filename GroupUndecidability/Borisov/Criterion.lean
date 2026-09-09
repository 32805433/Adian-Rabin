import GroupUndecidability.Borisov.Construction
import GroupUndecidability.Borisov.Mod5.Sparsity

/-!
# Borisov's simulation criterion

The forward implication is the relator calculation in `Construction.lean`.  The
converse is the complete normal-form argument, culminating in the mod-five
free-product syllable comparison that bounds a coefficient preimage by one
displayed rule letter.
-/

namespace Undecidability
namespace Borisov

/-- The deep normal-form direction in Borisov's simulation theorem. -/
theorem criterion_converse
    (datum : Thue.StandingDatum) (Q : List (Fin 2)) :
    (presentation datum).wordProblem (testWord Q) →
      ThueEq (Thue.systemOf datum.F datum.E) Q datum.P :=
  BorisovModFiveSparsity.criterion_converse datum Q

/-- Borisov's simulation theorem, specialized to the standing datum. -/
theorem criterion
    (datum : Thue.StandingDatum) (Q : List (Fin 2)) :
    ThueEq (Thue.systemOf datum.F datum.E) Q datum.P ↔
      (presentation datum).wordProblem (testWord Q) :=
  ⟨criterion_forward datum Q, criterion_converse datum Q⟩

end Borisov
end Undecidability
