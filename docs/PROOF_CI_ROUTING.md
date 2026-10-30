# Formal acceptance and current-paper checks

`python scripts/verify_eight_papers.py --historical-checks` checks every old formal/configuration byte, the entire historical manuscript relocation and all eight current identities. The editorial CI compiles the eight current manuscripts. For this exact migration, existing formal jobs reuse accepted source identities after the integrity gate; they do not perform an editorial-only clean multi-thousand-module rebuild. Workflow dispatch and source-changing formal work retain the original formal execution routes.

The legacy source verifiers keep their original mathematical/hash-checking cores. A small root resolver checks the current tree, then reconstructs the pinned historical paths and navigation in a temporary view. Formal compilation runners still operate on the actual unchanged current lean/ tree. New historical records and Lean namespaces are never rewritten.

The current [eight-route status](eight-papers/EIGHT_PAPER_FORMALIZATION_STATUS.md) is authoritative for reading scope. The fixed-ratio real-cycle proof remains PARTIAL, and the two-complex-coupling endpoint/transport proof is NOT_SEPARATELY_FORMALIZED. Both have independent mathematical manuscripts.
