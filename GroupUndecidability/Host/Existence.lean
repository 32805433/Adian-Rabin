import GroupUndecidability.Host.Tower

namespace Undecidability
namespace Host

/-- A three-generator, nine-relator host with the extra normal-weight-one property. -/
theorem exists_threeNineHost :
    ∃ P : FP 3 9,
      (∃ z : Word 3, P.NormallyGenerates z) ∧
        ¬ ComputablePred P.wordProblem := by
  obtain ⟨datum⟩ := Thue.exists_standingDatum
  exact ⟨presentationOf datum, ⟨zWord, z_normallyGenerates datum⟩,
    wordProblem_unsolvable datum⟩

end Host
end Undecidability
