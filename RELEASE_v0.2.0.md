# Ising bulk natural boundary: Lean formalization

This release completes the manuscript's internal form-factor proof chain and the absolute higher-even tail in Lean. The final physical statement retains the explicit real E1/E2 identification and published fixed-order E3 smoothness premises.

Core results are `IsingBulk.First.theorem_first`, `IsingBulk.Final.theorem_tail`, `IsingBulk.Final.theorem_nb`, and `IsingBulk.Final.theorem_nb_physical`. The reachable logical axiom union is `propext`, `Classical.choice`, and `Quot.sound`; theorem parameters remain explicit assumptions.

The proof-critical payload contains 1,071 production subtree modules plus the public root. Its identifier is `bf9e537fb5a963000ab1a7f1aef969144ba8e3fc7780b5cf1b56cba1c4bf37b2`.

Three internal adversarial review rounds used four newly created blind reviewers per round and a continuing adjudicator. Verification-tool findings were repaired with scoped regressions; the scientific payload stayed unchanged. These reviews are internal checks, not external peer review. Full reports, raw execution evidence, repair history and limitations are in the evidence assets.

Publication requires a successful full remote clean build, axiom/endpoint/control sequence and fresh kernel replay on the exact tagged commit. Asset manifests bind the source package, internal-review evidence, full remote execution evidence and hashes. Existing manuscript and historical release material are preserved.
