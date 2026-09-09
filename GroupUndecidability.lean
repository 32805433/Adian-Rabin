import GroupUndecidability.AdianRabin

namespace Undecidability

/-- There is a three-generator, nine-relator group with unsolvable word problem. -/
theorem exists_three_generator_nine_relator_group_with_unsolvable_word_problem :
    ∃ P : FP 3 9,
      ¬ ComputablePred P.wordProblem := by
  obtain ⟨P, _, hP⟩ := Host.exists_threeNineHost
  exact ⟨P, hP⟩

/--
There is an effective Adian--Rabin family for triviality whose members have four
generators and eleven relators.
-/
theorem exists_four_generator_eleven_relator_adian_rabin_family :
    ∃ A : ℕ → FP 4 11,
      FP.IsAdianRabinFamily A := by
  obtain ⟨datum⟩ := Thue.exists_standingDatum
  exact AdianRabin.exists_miller_tancer_family
    (Host.presentationOf datum) (2 : Fin 3)
      (Host.wordProblem_unsolvable datum) (by
        simpa [Host.zWord] using Host.z_normallyGenerates datum)

/--
There is an effective Adian--Rabin family for triviality whose members have two
generators and ten relators.
-/
theorem exists_two_generator_ten_relator_adian_rabin_family :
    ∃ A : ℕ → FP 2 10,
      FP.IsAdianRabinFamily A := by
  obtain ⟨datum⟩ := Thue.exists_standingDatum
  exact AdianRabin.exists_gordon_family
    (Host.presentationOf datum) (Host.gordonCondition21 datum)
      (Host.wordProblem_unsolvable datum)

end Undecidability
