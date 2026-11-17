# Ising 磁化率八篇论文

[当前八篇论文入口](papers/README.md) · [English](README.md) · [仓库地图](REPOSITORY_MAP.md) · [署名与 AI 使用披露](AUTHORSHIP.md)

八篇论文分属低温磁化率、高温磁化率、固定比值各向异性磁化率和双复耦合磁化率，每个主题各有两条证明。各篇研究全晶格磁化率，并采用相应的物理归一化。

固定比值原证明在等耦合时调用低温和高温原证明的归一化自然边界定理。实循环替代证明在文内处理等耦合情形。两篇双复耦合论文各自证明联合自然边界，证明每个有限正比值温度切片上的自然边界，并导出各向同性的圆盘与外域函数芽。

八条证明路线中有七条完成了 Lean 形式化。双复耦合端点／输运替代证明（JOINT-PSER）的状态为 `NOT_SEPARATELY_FORMALIZED`。[定理对应表](docs/eight-papers/LEAN_CORRESPONDENCE.md) · [八条路线状态](docs/eight-papers/EIGHT_PAPER_FORMALIZATION_STATUS.md)。

各向异性实循环证明（ANISO-PSER F002）的 Lean 定理是 `IsingBulk.AnisoF002.full_uniform_field_conclusion`。解析自然边界的条件是耦合为正。实温度磁化率识别和能量场响应以 `PublishedRealSpinFormFactors` 和 `PublishedRealGibbsFields` 为显式前提。[Lean 定理](lean/IsingBulk/AnisoF002/C03/FullUniformFieldConclusion.lean) · [F002 范围与审计](docs/aniso-f002/PUBLICATION.md)。

[Lean 源码](lean/) · [历史稿件与路径映射](archive/manuscripts/pre-eight-2026-10-30/README.md)

[本地验证指南](docs/PROOF_CI_ROUTING.md)列出历史核验、论文重编译、F002 编译和内核重放命令。

## Low-temperature susceptibility

- **A natural boundary for the low-temperature bulk square-lattice Ising susceptibility** (Original proof): [PDF](papers/low-temperature/original-proof/manuscript.pdf) · [TeX](papers/low-temperature/original-proof/manuscript.tex).
- **The full low-temperature Ising susceptibility: a regular-coordinate proof of the natural boundary** (Alternative regular-coordinate proof): [PDF](papers/low-temperature/alternative-proof/manuscript.pdf) · [TeX](papers/low-temperature/alternative-proof/manuscript.tex).
## High-temperature susceptibility

- **High-temperature bulk Ising susceptibility: a natural-boundary proof** (Original proof): [PDF](papers/high-temperature/original-proof/manuscript.pdf) · [TeX](papers/high-temperature/original-proof/manuscript.tex).
- **The complete high-temperature Ising susceptibility: a constrained-coordinate proof of the natural boundary** (Alternative constrained-coordinate proof): [PDF](papers/high-temperature/alternative-proof/manuscript.pdf) · [TeX](papers/high-temperature/alternative-proof/manuscript.tex).
## Fixed-ratio anisotropic susceptibility

- **Natural boundaries of the full bulk susceptibility for the fixed-ratio anisotropic square-lattice Ising model** (Original proof): [PDF](papers/fixed-ratio-anisotropy/original-proof/manuscript.pdf) · [TeX](papers/fixed-ratio-anisotropy/original-proof/manuscript.tex).
- **Natural boundaries of anisotropic Ising susceptibility via real-cycle pole estimates** (Alternative real-cycle proof): [PDF](papers/fixed-ratio-anisotropy/alternative-proof/manuscript.pdf) · [TeX](papers/fixed-ratio-anisotropy/alternative-proof/manuscript.tex).
## Susceptibility in two independent complex coupling variables

- **Natural boundaries of the full square-lattice Ising susceptibility in two complex coupling variables: Spectral domains and physical-slice restrictions** (Original proof): [PDF](papers/two-complex-couplings/original-proof/manuscript.pdf) · [TeX](papers/two-complex-couplings/original-proof/manuscript.tex).
- **Natural boundaries of the full square-lattice Ising susceptibility in two complex coupling variables: Endpoint geometry and constrained transport** (Alternative endpoint/transport proof): [PDF](papers/two-complex-couplings/alternative-proof/manuscript.pdf) · [TeX](papers/two-complex-couplings/alternative-proof/manuscript.tex).
