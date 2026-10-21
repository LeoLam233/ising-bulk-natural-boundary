# Natural boundaries of the square-lattice Ising susceptibility

**Two distinct proofs · Two temperature phases · One shared formal mathematics library**

This repository contains two separately developed natural-boundary proofs for the **complete zero-field bulk magnetic susceptibility** of the infinite isotropic square-lattice Ising model. Both concern the full lattice and infinite form-factor expansions. The proofs have different physical starting states, different particle-number sectors, and separate Lean verification entry points.

## Choose a proof

| **HIGH-TEMPERATURE PHASE** · Disordered state | **LOW-TEMPERATURE PHASE** · Ordered pure state |
|---|---|
| **Complete bulk susceptibility in the high-temperature Gibbs state** | **Connected bulk susceptibility in a low-temperature pure phase** |
| Physical interval: `0 < s < 1` | Physical interval: `s > 1` |
| **All odd-particle form factors**, summed to infinity | **All even-particle form factors**, summed to infinity; subtract spontaneous magnetization squared |
| Natural boundary: every point of `|s| = 1`, approached from `|s| < 1` | Natural boundary: every point of `|s| = 1`, approached from `|s| > 1` |
| [**Explore the high-temperature proof →**](high-temperature/README.md) | [**Explore the low-temperature proof →**](low-temperature/README.md) |
| [Mathematical manuscript](paper/ht/publication/manuscript.pdf) · [Lean theorem](lean/IsingBulk/HT/Final/PublishedPhysicalTheorem.lean) | [Mathematical manuscript](paper/next/manuscript.pdf) · [Lean proof entry](lean/IsingBulk.lean) |

Here `s = sinh(2βJ)`, `J > 0`. **Neither result is presented as a corollary of the other.** Each proof addresses its own complete physical observable and establishes noncancellation of its full particle expansion.

## How the repository is organized

| Area | What it contains |
|---|---|
| [**High-temperature proof**](high-temperature/README.md) | High-temperature theorem, complete manuscript, Lean proof, reproducibility and independent audits |
| [**Low-temperature proof**](low-temperature/README.md) | Low-temperature theorem, complete manuscript, Lean proof, reproducibility and historical releases |
| [**Shared Lean mathematics**](lean/IsingBulk/) | Reusable analytic, algebraic, contour and summability lemmas; no duplicate copy of the LT library |
| [**Proof and version map**](REPOSITORY_MAP.md) | Exact module ownership, frozen source boundaries and independent build targets |

The public-facing phase folders are **navigation**, while the proof files retain their audited Lean module paths and names. The low-temperature build remains `lean/IsingBulk.lean` with `lean/lakefile.toml`; the high-temperature build is `lean/IsingBulkHT.lean` with `lean/lakefile.ht.toml`. The latter reuses foundational LT mathematics without invoking the LT final natural-boundary theorem.

### Verification status

- **Low-temperature:** mathematical manuscript `v0.1-rc6`; Lean `v0.3.0-rc2`, with its own published Git history and verification records.
- **High-temperature:** frozen mathematical manuscript `HT-1.0`; Lean `1747`, with source-identical clean builds, fresh kernel replay and independent Pro/Codex adversarial audits reporting `EXHAUSTED`. The physical-germ theorem explicitly assumes the published real-temperature full-bulk form-factor identity.
- The two proof developments have not received independent human peer review; mathematical scope, external physical inputs, version identities and audit evidence are documented separately.

For reproducibility, begin at the relevant phase page rather than running both build targets together. Existing LT historical releases and their paths have not been renamed to accommodate the new HT proof.

[**中文首页**](README.zh.md) · [Authorship and provenance](AUTHORSHIP.md) · [Code license (MIT)](LICENSE) · [Document license (CC BY 4.0)](LICENSE-DOCUMENTATION.md)

Cite the results separately: [high-temperature citation](high-temperature/CITATION.cff) · [low-temperature citation](low-temperature/CITATION.cff). The [frozen HT manuscript](paper/ht/frozen/manuscript.pdf) and [editorial comparison](paper/ht/publication/README.md) remain available.
