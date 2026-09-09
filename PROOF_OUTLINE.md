# Proof outline

## The common `3/9` host

1. **Universal computation becomes finite rewriting.** The proof fixes an
   undecidable one-variable instance of Mathlib's universal partial-recursive
   evaluator and compiles it into a finitely supported one-tape machine.
   Binary-tape and Post-machine adapters then produce a finite Thue system, a
   computable input-word map, and a fixed target word such that reaching the
   target is equivalent to halting. A final reindexing replaces the finite
   alphabet and rule set by finite ordinal types.

2. **The seed becomes a synchronized three-rule system.** Matiyasevich's
   compression embeds the finite seed into a binary three-rule Thue system
   while preserving and reflecting the relevant fixed-target equivalence. The
   code `η(0) = 0110` and `η(1) = 01110` is then applied to every word. A
   boundary argument proves that rewrites cannot begin inside a codeword, so
   this second encoding also preserves and reflects equivalence. Its three
   pairs `Fᵢ = Eᵢ` and target `P` satisfy the additional support and killing
   conditions required later: every displayed word uses both letters, and the
   second relation forces both corresponding group elements to be trivial
   when they are inverses. These facts and fixed-target undecidability are
   packaged as `Thue.StandingDatum`.

3. **Borisov's simulator converts rewriting into a group word problem.** From
   a standing datum, the construction defines an explicit `FP 7 14`
   presentation and a test word of the form `[Q⁻¹tQ,k]`. Each Thue rewrite
   gives an elementary relator calculation, proving the forward implication.
   The converse is one of the substantial proofs in the project: iterated HNN
   normal forms, Britton pinches, exact double-coset control, coefficient
   classification, and a final mod-five sparsity argument recover a valid
   Thue derivation from triviality of the test word. Together they give
   `Borisov.criterion`:

   `Q` is equivalent to `P` in the Thue system if and only if Borisov's test
   word is trivial.

4. **The simulator is compressed injectively to `3/9`.** Two proper HNN
   embeddings and six Tietze eliminations leave the three generators `D,S,Z`
   and nine relators, defining `Host.presentationOf datum : FP 3 9`.
   Injectivity is proved rather than inferred from the substitutions: the
   Borisov group embeds successively into the final Borisov model and the
   `Y`- and `Z`-stage models. Interpreting `D,S,Z` in the `Z`-stage gives a map
   from the compressed host back to that model. The resulting commuting
   triangle, whose other side is already injective, forces the explicit
   compression homomorphism to be injective. Hence Borisov's test word is
   trivial exactly when its compressed host word is trivial.

5. **Undecidability is transferred to the host.** Combining the preceding
   equivalences yields `Host.thueEq_iff_testWord`. Since the host test-word map
   is computable, the undecidable fixed-target Thue predicate many-one reduces
   to the host word problem, proving `Host.wordProblem_unsolvable`. A separate
   quotient-by-normal-closure calculation shows that `Z` normally generates
   the host. Finally, `Host.exists_threeNineHost` packages this stronger
   normal-weight-one `FP 3 9` host; the first public theorem simply discards
   the extra normal-generator witness.

## The `4/11` Adian–Rabin family

The host has a displayed generator whose normal closure is the whole group.
The compressed Miller–Tancer reduction incorporates a formalized Tietze
elimination and changes `FP n m` to `FP (n + 1) (m + 2)`. Applied to the
`3/9` host, it produces a uniformly effective `FP 4 11` family with
undecidable triviality set.

## The `2/10` Adian–Rabin family

One host generator is trivial in the abelianization, which verifies Gordon's
Condition (2.1). Gordon's Lemma 2.1 then converts the same `3/9` host into a
uniformly effective `FP 2 10` family with undecidable triviality set.
