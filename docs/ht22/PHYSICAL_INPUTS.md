# Exact external physical premise and new physical germ

The parameter-free aggregate is `IsingBulk.HT22.ht22_full_target`.
Its abstract analytic conclusions concern the explicitly constructed angular
observable, not an arbitrarily named function. The `physical_input` field
connects that observable to a supplied real correlation function under exactly
`PhysicalScope.PublishedRealHTSpinFormFactors corr`.

The predicate has two fields, both only for real 0<s<1:

1. `spin_square`: `corr s (0,0) = 1`.
2. `sitewise`: for every lattice site v, the complexification of `corr s v`
   equals the established HT interior prefactor times the infinite sum over
   **all positive odd** published `physicalFullLatticeCoefficient (2*n+1) s⁻¹ v`.

There are no external assumptions about complex continuation, absolute lattice
summability, tail derivatives, covariance/coarea, singular coefficients,
noncancellation or a natural boundary. The zero-field HT interpretation has no
LT magnetization subtraction. The published real-temperature identity is a
physics input, not newly derived here from a Gibbs-measure construction.

`PhysicalScope.RealSpin` proves absolute summability and the full lattice sum,
including its origin contribution of exactly one, from the scoped premise and
the internally established joint lattice/particle bound. Its beta normalization
is `arsinh(s)/(2*J)`, with every J>0, and it proves the inverse coordinate relation.
The source itself and AuditHT22 print the complete literal types.

`Physical.ExteriorIdentity` proves the new finite angular coefficients equal the
existing published coefficients, using real-interval identities and analytic
uniqueness. `Physical.GermBridge` identifies the full angular sums, constructs the
removable extension at s=0 by an actual proved complex limit, and proves equality
of both new analytic germs to their existing counterparts on the whole unit
disk. The beta-inclusive identity uses multiplication, never division by beta
at the origin.

`Final.NaturalBoundary` then derives the boundary from the new finite FIRST,
finite lower complement, and complete infinite differentiated-tail proofs.
The old HT terminal natural-boundary/noncancellation/full-tail endpoints are
forbidden substitutes. The definitive check of their absence is the post-freeze
complete type/value/structural-support scan, not import-path inspection.

The publication CI checks the literal elaborated predicate and all fourteen stored proof arguments, separately from the completed AI audits. [Frozen authority](../../archive/manuscripts/pre-eight-2026-10-30/paper/ht/pser/README.md) · [Correspondence](PROOF_MAP.md).
