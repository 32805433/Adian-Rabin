# Axiom audit

Date: 2026-09-08

## Scope and method

This audit covers the active `GroupUndecidability` library and its three public
theorems in `GroupUndecidability.lean`. It excludes dependencies, the standalone
comparator package, generated artifacts, and `archive/`.

Two checks are used:

1. `AxiomAudit.lean` applies Lean's transitive `#print axioms` command to the
   three public theorems.
2. A recursive source scan checks every active Lean file for project axioms,
   proof placeholders, and `opaque` or `unsafe` declarations.

Because `#print axioms` is transitive, these three checks already cover every
intermediate construction used by the public results; no subsystem needs a
separate entry.

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

## Reproduction

```sh
lake env lean AxiomAudit.lean
lake build GroupUndecidability
rg -n '^\s*(axiom|constant)\b|\bsorry\b|\badmit\b|sorryAx|^\s*opaque\b|^\s*unsafe\b' \
  GroupUndecidability.lean GroupUndecidability AxiomAudit.lean -g '*.lean'
```

The final command should return no matches.
