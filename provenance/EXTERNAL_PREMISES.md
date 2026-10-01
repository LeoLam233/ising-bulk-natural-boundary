# External premises and citation roles

The paper is conditional on the standard physical correlation representation and magnetization formula described below, and uses the fixed-order theorem only where applicable. No AI verdict or prior project notebook is an external theorem.

| Key | Source and locator | Role / limit |
|---|---|---|
| E1 | [Palmer–Tracy 1981](https://doi.org/10.1016/0196-8858(81)90010-5), Cor. 2.0 p. 351; Thm 4.1 p. 361; Thm 5.0 p. 374 and proof pp. 375–378. [Published TW2014](https://doi.org/10.1007/s10955-014-1061-4), Eq. (3) pp. 1126–1127 and Appendix 1 (7)–(8) pp. 1132–1133. | Low-temperature Fredholm correlation representation in the infinite-volume + boundary-condition state. The state, determinant convention, normalized measures and exact full-site/offsite relation were checked for this local integration; see [E1 closure](E1_SOURCE_CLOSURE.md). The original correlation theorem remains an external input; no infinite-tail theorem is supplied. |
| E2 | [Yang 1952](https://doi.org/10.1103/PhysRev.85.808) | Low-temperature spontaneous magnetization. Its selected local/exterior branch is specified in the manuscript. Bibliographic attribution is not a new proof of this input. |
| E3 | [Published Tracy–Widom 2014](https://doi.org/10.1007/s10955-014-1061-4), fixed-even-order theorem, p. 1127 | Smooth extension away from the fixed order's Nickel set. It is not invoked as smoothness at the selected Nickel point or as an estimate uniform in the infinite particle tail. The paper's local complement argument is an internal obligation. |
| X1 | [Boukraa et al. 2008](https://arxiv.org/abs/0808.0763), equations (4)–(9) | Independent full-site angular formula comparison in Appendix F, not a proof of the candidate bulk noncancellation bound. |
| X2 | [McCoy–Maillard 2012](https://arxiv.org/abs/1203.1456), definitions and amplitude conventions | Physical response and comparison conventions. The displayed review amplitude is not assumed to prove the manuscript's internal nonzero coefficient. |
| H1 | [Wu–McCoy–Tracy–Barouch 1976](https://doi.org/10.1103/PhysRevB.13.316) | Expansion genealogy; not a substitute for the explicit normalization in Appendix F. |
| H2 | [Guttmann–Enting 1996](https://doi.org/10.1103/PhysRevLett.76.344) | Historical numerical evidence, not a full natural-boundary theorem. |
| H3 | [Nickel 1999](https://doi.org/10.1088/0305-4470/32/21/303), [2000](https://doi.org/10.1088/0305-4470/33/8/313) | Fixed-particle singularity history. The selected first-order family is proved internally in §3; the manuscripts' full publisher texts were not comprehensively re-audited in this release pass. |
| H4 | [Tracy–Widom 2013](https://arxiv.org/html/1307.5913v3) | Established diagonal-susceptibility natural boundary and noncancellation method. Different observable from the full lattice sum. |
| H5 | [Tracy–Widom 2015/2017](https://arxiv.org/html/1502.04922v1) | Closely related Toeplitz-sum proof methods, examined in Sections III–IV. Does not directly prove the present bulk estimates. |

The claim that the ordinary double-contour measure is `(2πi)^(-2N)/N!` is derived from normalized angular and auxiliary-residue measures in Appendix F. It agrees with the published Eq. (3). That coefficient includes the origin and equals `f00^(N)+2T_N` at fixed even `N`. The earlier arXiv-v1 discrepancy is recorded only as [version history](E1_SOURCE_CLOSURE.md).

Standard algebra, Schur/Pfaffian identities, beta integrals and cyclotomic facts used by the manuscript are either derived or explicitly displayed there. An omitted derivation, if found, must be assessed on its merits rather than justified by an audit PASS. The [historical rc2 source-scope record](bibliographic_scope_rc2.json) covers the twelve references of manuscript v0.1-rc2. [bibliographic_scope.json](bibliographic_scope.json) is preserved as a historical rc1-era scope record.
