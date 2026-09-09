import GroupUndecidability.AdianRabin.MillerTancer.Compressed

/-! The Adian--Rabin family obtained from the compressed Miller--Tancer construction. -/

namespace Undecidability.MillerTancer.Compressed

/-- Natural-number-indexed compressed Miller--Tancer family. -/
def family (P : FP n m) (k : Fin n) : ℕ → FP (n + 1) (m + 2) :=
  fun j => Compressed.transform P k (wordOfNat n j)

/-- The compressed family is an effective Adian--Rabin family. -/
theorem family_isAdianRabin (P : FP n m) (k : Fin n)
    (hP : ¬ ComputablePred P.wordProblem)
    (hk : P.NormallyGenerates (Word.generator k)) :
    FP.IsAdianRabinFamily (family P k) :=
  isAdianRabinFamily_of_wordProblem_reduction P (Compressed.transform P k)
    hP (transform_computable P k) (presentsTrivial_transform_iff P k hk)

end Undecidability.MillerTancer.Compressed
