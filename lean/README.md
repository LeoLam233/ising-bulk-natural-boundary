# Lean formalizations

[Eight-route status](../docs/eight-papers/EIGHT_PAPER_FORMALIZATION_STATUS.md) ·
[Actual theorem and field correspondence](../docs/eight-papers/LEAN_CORRESPONDENCE.md) ·
[Current verification and build commands](../docs/PROOF_CI_ROUTING.md)

The independent ANISO-PSER F002 real-cycle proof is complete at
[`IsingBulk.AnisoF002.full_uniform_field_conclusion`](IsingBulk/AnisoF002/C03/FullUniformFieldConclusion.lean).
The final audit entry is
[`IsingBulk.AnisoF002.Audit.C03FinalReplayBundle`](IsingBulk/AnisoF002/Audit/C03FinalReplayBundle.lean).
The [F002 publication record](../docs/aniso-f002/PUBLICATION.md) states the
two explicit published-real interfaces and links to the type contract.

The earlier LT, HT, ANISO C001, JOINT C002, LT22 and HT22 proof sources and
their Lake configurations are preserved. They use the same Lean 4.34.1
toolchain and dependency lock as F002. See the linked status and build guide for
the separate endpoints and acceptance routes.

The [pre-migration technical README](https://github.com/LeoLam233/ising-bulk-natural-boundary/blob/923266754afd65f5922a51f59a72ca56e1a88942/lean/README.md)
retains the older build instructions in their original layout. Historical
manuscript paths are indexed in the [archive](../archive/manuscripts/pre-eight-2026-10-30/README.md).
