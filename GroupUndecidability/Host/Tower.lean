import GroupUndecidability.Host.Compression
import GroupUndecidability.GroupTheory.HNNLemmas
import GroupUndecidability.Borisov.Criterion
import GroupUndecidability.Host.CompressionInjective

namespace Undecidability
namespace Host

/--
The two proper HNN embeddings and the six Tietze eliminations preserve the
truth of Borisov's test word.
-/
theorem borisov_testWord_iff_compressed
    (datum : Thue.StandingDatum) (Q : List (Fin 2)) :
    (Borisov.presentation datum).wordProblem (Borisov.testWord Q) ↔
      (presentationOf datum).wordProblem (testWord Q) :=
  Compression.testWord_iff datum (compression_injective datum) Q

/-- The Thue predicate is represented by the compressed host test word. -/
theorem thueEq_iff_testWord
    (datum : Thue.StandingDatum) (Q : List (Fin 2)) :
    ThueEq (Thue.systemOf datum.F datum.E) Q datum.P ↔
      (presentationOf datum).wordProblem (testWord Q) :=
  (Borisov.criterion datum Q).trans
    (borisov_testWord_iff_compressed datum Q)

/-- Normal generation from Proposition 2.4 of the paper, proved in the
compressed presentation. -/
theorem z_normallyGenerates (datum : Thue.StandingDatum) :
    (presentationOf datum).NormallyGenerates zWord := by
  let P := presentationOf datum
  let N : Subgroup P.Group :=
    Subgroup.normalClosure ({P.evalWord zWord} : Set P.Group)
  let q : P.Group →* P.Group ⧸ N := QuotientGroup.mk' N
  let x : Fin 3 → P.Group ⧸ N := fun i => q (PresentedGroup.of i)
  have hz : x 2 = 1 := by
    apply (QuotientGroup.eq_one_iff _).2
    apply Subgroup.subset_normalClosure
    change PresentedGroup.of (2 : Fin 3) ∈ ({P.evalWord zWord} : Set P.Group)
    simp [FP.evalWord, zWord]
  have hrel (i : Fin 9) : Word.eval x (P.relator i) = 1 := by
    have h := congrArg q (P.relator_eq_one i)
    change q (Word.eval (fun j => PresentedGroup.of j) (P.relator i)) = q 1 at h
    rw [Word.map_eval] at h
    change Word.eval (q ∘ fun j => PresentedGroup.of j) (P.relator i) = 1
    simpa only [map_one] using h
  have h8 := hrel 8
  simp [P, presentationOf, presentation, rho, oldSurvivingRelator,
    OldWord.evaluate_relation, OldWord.evaluate_inverse,
    OldWord.evaluate_product, tau, yWord, cWord, tWord, eWord, dWord,
    zWord, hz, Word.product] at h8
  have hd2 : x 0 * x 0 = 1 := by
    calc
      x 0 * x 0 = (x 0)⁻¹⁻¹ * (x 0)⁻¹⁻¹ :=
        congrArg₂ (fun a b => a * b) (inv_inv _).symm (inv_inv _).symm
      _ = ((x 0)⁻¹ * (x 0)⁻¹)⁻¹ :=
        (mul_inv_rev (x 0)⁻¹ (x 0)⁻¹).symm
      _ = 1 := by rw [h8]; simp
  have hd4 : x 0 ^ 4 = 1 := by
    calc
      x 0 ^ 4 = (x 0 * x 0) * (x 0 * x 0) := by
        simp [pow_succ, mul_assoc]
      _ = 1 := by rw [hd2]; simp
  have hd := hrel 0
  simp [P, presentationOf, presentation, rho, oldSurvivingRelator,
    OldWord.evaluate_relation, OldWord.evaluate_product,
    OldWord.evaluate_inverse, OldWord.evaluate_pow, tau, dWord, sWord,
    hd4, Word.product] at hd
  have hsimulation := hrel 4
  simp [P, presentationOf, presentation, rho, oldSurvivingRelator,
    oldSimulationRelator, OldWord.evaluate_relation,
    OldWord.evaluate_product, OldWord.evaluate_inverse,
    OldWord.evaluate_pow, OldWord.evaluate_positive, tau, dWord, eWord,
    yWord, cWord, tWord, sWord, s2Word, zWord, hz, hd,
    Word.product] at hsimulation
  have hFE :
      Thue.evalPositive (x 1) (x 1)⁻¹ (datum.F 1) =
        Thue.evalPositive (x 1) (x 1)⁻¹ (datum.E 1) :=
    eq_of_mul_inv_eq_one hsimulation
  have hs : x 1 = 1 :=
    (datum.kill (x 1) (x 1)⁻¹ rfl hFE).1
  have hx (i : Fin 3) : x i = 1 := by
    fin_cases i
    · exact hd
    · exact hs
    · exact hz
  have hq : q = 1 := by
    apply PresentedGroup.ext
    intro i
    change q (PresentedGroup.of i) = 1
    exact hx i
  have hsub : Subsingleton (P.Group ⧸ N) := by
    constructor
    intro a b
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective N a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective N b
    change q a = q b
    rw [hq]
    rfl
  have hN : N = ⊤ := QuotientGroup.subsingleton_iff.mp hsub
  unfold FP.NormallyGenerates
  simpa only [P, N, FP.evalWord_eq_mk] using hN

/-- The explicit compressed host has unsolvable word problem. -/
theorem wordProblem_unsolvable (datum : Thue.StandingDatum) :
    ¬ ComputablePred (presentationOf datum).wordProblem := by
  apply not_computablePred_of_manyOneReducible datum.undecidable
  exact ⟨testWord, testWord_computable, thueEq_iff_testWord datum⟩

end Host
end Undecidability
