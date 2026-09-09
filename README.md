# A Small Group with Unsolvable Word Problem and Small Adian–Rabin Families

This Lean 4 project gives formal proofs of three quantitative results
about finitely presented groups:

1. There exists a 3-generator, 9-relator group with unsolvable word
   problem.

2. There exists an Adian–Rabin family of 4-generator, 11-relator group
   presentations.

3. There exists an Adian–Rabin family of 2-generator, 10-relator group
   presentations.

Their exact Lean statements are:

```lean
theorem exists_three_generator_nine_relator_group_with_unsolvable_word_problem :
    ∃ P : FP 3 9,
      ¬ ComputablePred P.wordProblem

theorem exists_four_generator_eleven_relator_adian_rabin_family :
    ∃ A : ℕ → FP 4 11,
      FP.IsAdianRabinFamily A

theorem exists_two_generator_ten_relator_adian_rabin_family :
    ∃ A : ℕ → FP 2 10,
      FP.IsAdianRabinFamily A
```

Here `FP n m` is a finite presentation with exactly `n` generator slots and
`m` relator slots. `FP.IsAdianRabinFamily A` says that the relators of `A` are
uniformly computable and that the set of indices presenting the trivial group
is undecidable.

All three declarations are exported by
[`GroupUndecidability.lean`](GroupUndecidability.lean), under the namespace
`Undecidability`. The active library contains no project-specific axioms or
proof placeholders. Its transitive kernel audit reports only Lean's standard
principles `propext`, `Classical.choice`, and `Quot.sound`; see
[`AXIOM_AUDIT.md`](AXIOM_AUDIT.md). For a self-contained formalization of the
statements and the definitions needed to check them, see
[`comparator/Challenge.lean`](comparator/Challenge.lean).

The public Adian–Rabin interface also provides two reusable reductions in
[`GroupUndecidability/AdianRabin.lean`](GroupUndecidability/AdianRabin.lean):

- `AdianRabin.exists_miller_tancer_family`, from a finite presentation with
  unsolvable word problem and a displayed normal generator to an
  `FP (n + 1) (m + 2)` Adian–Rabin family;

- `AdianRabin.exists_gordon_family`, from a finite presentation satisfying
  Gordon's Condition (2.1) and having unsolvable word problem to an
  `FP 2 (m + 1)` Adian–Rabin family.

## Build and use

The project pins Lean and Mathlib at version 4.32.2. From the repository root:

```sh
lake exe cache get
lake build
lake env lean AxiomAudit.lean
```

The cache command is needed only when the matching Mathlib build artifacts are
not already installed. To use the results from another project:

```lean
import GroupUndecidability

#check Undecidability.exists_three_generator_nine_relator_group_with_unsolvable_word_problem
#check Undecidability.exists_four_generator_eleven_relator_adian_rabin_family
#check Undecidability.exists_two_generator_ten_relator_adian_rabin_family
```

## Repository layout

| Path | Role |
| --- | --- |
| [`GroupUndecidability.lean`](GroupUndecidability.lean) | Public root module and the three main theorems |
| [`GroupUndecidability/`](GroupUndecidability/) | Active formal proof library |
| [`AxiomAudit.lean`](AxiomAudit.lean), [`AXIOM_AUDIT.md`](AXIOM_AUDIT.md) | Executable kernel audit and its recorded result |
| [`PROOF_OUTLINE.md`](PROOF_OUTLINE.md) | Outline of the three formalized proofs |
| [`comparator/`](comparator/) | Self-contained statements, solution, and Lean Comparator configuration |
| [`lakefile.toml`](lakefile.toml), [`lake-manifest.json`](lake-manifest.json), [`lean-toolchain`](lean-toolchain) | Project configuration and pinned Lean/Mathlib dependencies |

## Proof-library layout

The structure inside [`GroupUndecidability/`](GroupUndecidability/) is:

| Path | Role |
| --- | --- |
| [`Presentation.lean`](GroupUndecidability/Presentation.lean), [`Computability.lean`](GroupUndecidability/Computability.lean) | Finite-presentation and computability foundations |
| [`Machine/`](GroupUndecidability/Machine/) | Fixed universal machine and the machine-to-rewriting reduction |
| [`Thue/`](GroupUndecidability/Thue/) | Finite Thue seed, three-rule compression, synchronization, and final standing datum |
| [`GroupTheory/`](GroupUndecidability/GroupTheory/) | Shared free-product and HNN-extension infrastructure |
| [`Borisov/`](GroupUndecidability/Borisov/) | Borisov's group simulator and its word-problem criterion |
| [`Host/`](GroupUndecidability/Host/) | Construction and analysis of the explicit `FP 3 9` host |
| [`AdianRabin.lean`](GroupUndecidability/AdianRabin.lean) | Public interface to both Adian–Rabin reductions |
| [`AdianRabin/MillerTancer/`](GroupUndecidability/AdianRabin/MillerTancer/) | Compressed `FP 4 11` family |
| [`AdianRabin/Gordon/`](GroupUndecidability/AdianRabin/Gordon/) | Gordon's Lemma 2.1 and the `FP 2 10` family |

The facade modules [`Borisov.lean`](GroupUndecidability/Borisov.lean) and
[`Host.lean`](GroupUndecidability/Host.lean) expose the corresponding core
developments. The principal construction endpoints are
`Thue.exists_standingDatum`, `Borisov.criterion`, and
`Host.exists_threeNineHost`.

## References

The following published sources supplied inputs and background:

| Source | Use in the development |
| --- | --- |
| [Borisov (1969)](https://doi.org/10.1007/BF01101402) | Group simulator and the `3/9` host construction |
| [Britton (1958)](https://doi.org/10.1112/plms/s3-8.4.493) | HNN normal-form arguments |
| [Carneiro (2019)](https://doi.org/10.4230/LIPIcs.ITP.2019.12) | Background for Mathlib's partial-recursive framework |
| [Gordon (2022)](https://doi.org/10.53733/205) | Gordon reduction yielding a `2/10` Adian–Rabin family |
| [Matiyasevich (1995)](https://doi.org/10.1007/3-540-59340-3_4) | Compression to a three-rule Thue system |
| [Miller (1992)](https://doi.org/10.1007/978-1-4613-9730-4_1) and [Tancer (2023)](https://arxiv.org/abs/2310.07421) | The original Miller–Tancer reduction |
| [Post (1947)](https://doi.org/10.2307/2267170) | Machine-to-Thue reduction |

## AI authorship

Essentially all of the Lean source, supporting scripts, and project
documentation in this repository was produced by GPT-5.6 Sol in Codex,
under the direction and review of the author.

## License

The repository's own code and documentation are under the [MIT license](LICENSE).
Lean, Mathlib, and their dependencies retain their respective licenses.
