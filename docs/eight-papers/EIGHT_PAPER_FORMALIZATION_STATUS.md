# Eight distinct proof routes

| Subject | Proof | Status | Actual formal anchor / limitation |
|---|---|---|---|
| Low-temperature susceptibility | Original | COMPLETED_WITH_EXPLICIT_SCOPE | `IsingBulk.Final.theorem_nb`; `theorem_nb_physical`, E1/E2 and real x>16 |
| Low-temperature susceptibility | Alternative regular-coordinate | COMPLETED_WITH_EXPLICIT_SCOPE | `IsingBulk.Preferred22.preferred_full_target : PreferredFullTarget`; five conjunction groups |
| High-temperature susceptibility | Original | COMPLETED_WITH_EXPLICIT_SCOPE | `IsingBulk.HT.Final.publishedPhysicalSusceptibility_germ_natural_boundary`; real representation antecedent |
| High-temperature susceptibility | Alternative constrained-coordinate | COMPLETED_WITH_EXPLICIT_SCOPE | `IsingBulk.HT22.ht22_full_target : HT22FullTarget`; fourteen actual fields |
| Fixed-ratio anisotropic susceptibility | Original | COMPLETED_WITH_EXPLICIT_SCOPE | `IsingBulk.Anisotropic.full_uniform_field_conclusion`; real form-factor and separate Gibbs premises; original normalized isotropic imports |
| Fixed-ratio anisotropic susceptibility | Alternative real-cycle | COMPLETED_WITH_EXPLICIT_SCOPE | [`IsingBulk.AnisoF002.full_uniform_field_conclusion`](../../lean/IsingBulk/AnisoF002/C03/FullUniformFieldConclusion.lean); internal equal-coupling proof and explicit published-real form-factor and Gibbs premises for the real physical fields |
| Susceptibility in two independent complex coupling variables | Original | COMPLETED_WITH_EXPLICIT_SCOPE | `IsingBulk.Joint.full_joint_conclusion`; eleven top-level fields, seven core structures |
| Susceptibility in two independent complex coupling variables | Alternative endpoint/transport | NOT_SEPARATELY_FORMALIZED | No independently completed Lean certificate for this F001 argument |

Seven of the eight routes are complete at the scopes in the [current theorem correspondence](LEAN_CORRESPONDENCE.md). The [F002 publication record](../aniso-f002/PUBLICATION.md) covers the new seventh route. The [six-route scope matrix](SIX_PAPER_LEAN_SCOPE_MATRIX.csv) records the earlier migration. Each manuscript has its own argument and physical interfaces; JOINT-PSER retains its separate manuscript proof.
