# Axiom audit

Last checked: 2026-09-09.

## Scope and method

This audit covers the active `GroupUndecidability` library and its three public
theorems in `GroupUndecidability.lean`. The kernel-axiom check follows all
transitive proof dependencies, including imported libraries. The source scan
covers only the project proof library and `AxiomAudit.lean`; it excludes
third-party source files, generated artifacts, and the independent
`Challenge.lean` statement file.

The independent `Challenge.lean` file contains three intentional theorem
holes. They are not imported by the proof library and do not count as
unresolved proof placeholders.

Two checks are used:

1. `AxiomAudit.lean` applies Lean's transitive `#print axioms` command to the
   three public theorems.
2. A recursive source scan checks every active Lean file for project axioms,
   proof placeholders, and `opaque` or `unsafe` declarations.

Because `#print axioms` is transitive, the checks of the three public theorems
cover every intermediate construction used by those results.

## Result

The source scan found no project-defined axiom or proof placeholder in the
active formalization. The kernel results are:

| Public theorem | Kernel axioms |
| --- | --- |
| `exists_three_generator_nine_relator_group_with_unsolvable_word_problem` | `propext`, `Classical.choice`, `Quot.sound` |
| `exists_four_generator_eleven_relator_adian_rabin_family` | `propext`, `Classical.choice`, `Quot.sound` |
| `exists_two_generator_ten_relator_adian_rabin_family` | `propext`, `Classical.choice`, `Quot.sound` |

These are standard Lean/Mathlib logical axioms. No unproved mathematical
assumption introduced by this project occurs in any public theorem.

A separate local check on 2026-09-09 confirmed that the three proved
declarations match the independent statements in `Challenge.lean` and
passed Lean kernel replay. Independent NanoDa replay was not performed.

## Reproduction

```sh
lake build GroupUndecidability
lake env lean AxiomAudit.lean
rg -n '^\s*(axiom|constant)\b|\bsorry\b|\badmit\b|sorryAx|^\s*opaque\b|^\s*unsafe\b' \
  GroupUndecidability.lean GroupUndecidability AxiomAudit.lean -g '*.lean'
```

The final command should return no matches.
