# LT22 theorem and physical scope

The frozen [22-page paper](../../archive/manuscripts/pre-eight-2026-10-30/paper/lt/pser/manuscript.pdf) has the independent root [FullTheorem.lean](../../lean/IsingBulk/Preferred22/FullTheorem.lean), imported by [Preferred22.lean](../../lean/IsingBulk/Preferred22.lean):

```lean
IsingBulk.Preferred22.preferred_full_target : IsingBulk.Preferred22.PreferredFullTarget
```

The elaborated terminal type has no root premises. The [target definition](../../lean/IsingBulk/Preferred22/LatticeAssembly.lean) conjoins the exact joint lattice/particle summability and coefficient identity, scoped physical identification, exterior analyticity, all-circle nonextension and physical-sheet nonextension.

| Mathematical scope | Formal correspondence |
|---|---|
| All lattice sites, including origin; every positive even order; genuine infinite sum | `PreferredLatticeFubiniStatement`, `preferred_lattice_fubini`, `PreferredFullTarget`; joint norm summability in `JointSiteSummability.lean` |
| Correct connected pure-phase susceptibility | `connectedLatticeSum` subtracts the squared magnetization within each lattice summand; physical equality uses Bool-indexed plus/minus phases for every real x > 1 |
| Published real-temperature inputs | `YangInput` and `PalmerTracyInput`, packaged by `PublishedPhysicalInputs`; antecedents only in the physical identification conjunct |
| Actual first nonzero singularity, finite lower orders and complete differentiated higher tail | `preferred_actual_first_singularity`, `preferred_actual_finite_complement`, `preferred_actual_absolute_tail`; assembled in `preferred_selected_analytic_obligations` |
| Nonextension at every unit-circle point, including axes | `preferred_bulk_natural_boundary`; actual `bulkFunction` and `HasExteriorExtension` |
| Physical inverse-temperature sheets, including approach sets at ±i, for every J > 0 | `preferred_physical_bulk_natural_boundary`, `HasPhysicalBoundaryExtension` |

The physical contract uses the precisely typed Yang magnetization and Palmer–Tracy real-temperature correlation interfaces. It does not assert an additional formal construction of Gibbs states. The root does not require an old LT final susceptibility-boundary endpoint or the historical arc-length corollary. Reused foundations are the exact 153 inherited modules; the previously audited stored type/value/structural dependency graph is pinned in [AUDITED_GRAPH.json](../../provenance/lt22/AUDITED_GRAPH.json). Fresh integration acceptance requires equality with that graph, zero missing/unsafe/partial declarations, and exactly `propext`, `Classical.choice`, `Quot.sound` as reachable axioms.

The October 25 verdict is EXHAUSTED for the frozen object. It reports internal audit exhaustion and source/kernel acceptance, without claiming external human peer review or novelty clearance. [Prior acceptance](../../provenance/lt22/PRIOR_ACCEPTANCE.json) and [new integration verification](BUILD_AND_VERIFY.md) have separate execution identities.
