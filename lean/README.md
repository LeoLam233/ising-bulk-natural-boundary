# Ising bulk natural boundary: Lean formalization

This source formalizes the pinned manuscript's original form-factor chain and the internally proved absolute higher-even tail. The physical identification and published fixed-order smoothness interfaces remain explicit premises.

Core declarations:

- `IsingBulk.First.theorem_first`: first-particle singular asymptotic and lower even orders.
- `IsingBulk.Final.theorem_tail`: the literal infinite sum of norms of every permitted derivative of the higher even form factors is little-o of the first singular scale.
- `IsingBulk.Final.theorem_nb`: no local holomorphic continuation of the constructed exterior normalized bulk series through any unit-circle point, conditional on the explicit published fixed-order interface.
- `IsingBulk.Final.theorem_nb_physical`: physical germ identification and boundary nonextension, conditional on E1, E2, and the same fixed-order interface, with positive coupling.

The reachable axiom union is `propext`, `Classical.choice`, and `Quot.sound`. The formalization does not construct the infinite-volume probability measure or reprove the external physics publications.

## Reproduction and evidence scope

Lean 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`, and all nine dependency revisions are frozen. There are 1,071 production subtree modules and the public root, totaling 1,072 production `.lean` files.

The proof-critical payload ID is `bf9e537fb5a963000ab1a7f1aef969144ba8e3fc7780b5cf1b56cba1c4bf37b2`. Its exact bytes were used for the independently executed clean project build, 9,199 declaration/axiom checks, endpoint and positive/negative controls, and full `leanchecker --fresh --verbose IsingBulk` replay. The supplied execution records and artifact hashes bind those results under the documented trusted-operator/runtime/distribution assumptions.

The remote acceptance workflow checks the full payload and dependency pins and actually builds `IsingBulk.Algebra.SchurPfaffian`. It is a production smoke/infrastructure check, not a repeated whole-project kernel replay. Mathematical payload identity and complete release-tree identity are recorded separately.

Three internal adversarial rounds are complete for this unchanged scientific payload, with recorded verification-only repairs. A separate full remote final-commit build, axiom/endpoint/control sequence and fresh kernel replay is required before the v0.2.0 tag and Release. See the release evidence assets for exact receipts and limitations. Internal adversarial review is not independent external peer review or an absolute guarantee.
