# Current candidate controls

The seven ordinary Lean controls are PositiveArithmetic, PositiveInterfaces,
InternalRegularity, E3Guard and three intentional-invalid fixtures. They check
actual applications through the public root and exact expected failure locations.
InternalRegularity traverses compiled canonical theorem types and proof bodies
to exclude E3 and require the internal replacement. E3Guard remains a control of
the legitimate historical comparison interface, not a canonical premise.

run_dependency_control.py adds a separate adversarial test: an unused E3
parameter on an otherwise valid NB wrapper must be rejected by that same
compiled dependency traversal. It mutates a fresh temporary fixture only.

The 13 manifest and 13 production-verifier regressions retain their bounded
scope. Before/after identities bind the current source and checking context.
Import, memory, timeout, recursion and interruption failures cannot count as
successful mathematical negatives. Generated fixtures/results are never
production imports or proof-critical source inventory entries.

Historical launcher notes and prior counts are byte-preserved in
[history/v0.2.1](../../history/v0.2.1/control_packet/continuation/README.md).
Exact new executions belong to [validation](../../../release/next/VALIDATION.json).
