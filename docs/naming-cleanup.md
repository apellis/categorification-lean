# Naming cleanup

A deferred maintenance item, to be done in one pass rather than piecemeal: renaming
modules low in the import graph rebuilds most of the library, so the renames are batched into
a single change.

Names of declarations and modules should describe the mathematics (AGENTS.md, "Lean
engineering"). Source locators belong in docstrings, where they are required, and not in names:
they go stale when a source is renumbered between versions.

## Scope

1. **Theorem numbers in declaration names.** About 190 declarations, for example
   `lemma_5_4_i`, `lemma_5_4_iii_printed_false`, `thm_3_17`, `prop_2_5_sl2`, `cor_3_16_f`
   (Khovanov–Lauda I–III, crystals, quantum groups). Rename by content; keep the locator in the
   docstring.
2. **Theorem numbers in module names.** 38 files, for example
   `WeightedKLR/RedStrands/Prop55*.lean` (Webster Prop 5.5), `Prop328*`, `Lemma39*`, `Thm317*`.
3. **Process adjectives.** About 40 declarations containing "actual" or "original", for example
   `actualRelativeDifferential`, `actualMate`, `originalMateEquiv_natural`.

## Procedure

- Regenerate the inventory at the time of the pass (the counts above were taken on 2026-11-25).
- One PR, with the old → new names listed in the commit message ("API changes: old → new").
- Update the README, the roadmaps under `docs/`, `scripts/NonVacuity.lean` and
  `scripts/AxiomAudit.lean` in the same PR, and the `\lean{...}` references in downstream
  repositories when they next bump their pin.
