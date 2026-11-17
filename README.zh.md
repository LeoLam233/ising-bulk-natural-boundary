# Ising 磁化率八篇论文

[当前八篇论文入口](papers/README.md) · [English](README.md) · [仓库地图](REPOSITORY_MAP.md)

四个主题各有两条不同的数学证明：低温磁化率、高温磁化率、固定比值各向异性磁化率，以及两个独立复耦合变量下的磁化率。入口列出八篇真实学术标题及 PDF/TeX；作者信息和论文内 ChatGPT 声明均保留。

原始固定比值证明在等耦合处合法调用原始低温、高温归一化自然边界定理；其实循环替代证明在文内独立处理等耦合情形。两篇双复变量证明各自证明联合结论、所有正比值切片及等耦合下降，未用环境空间非延拓代替切片证明。

八条路线中有七条已在 Lean 完成，[定理对应表](docs/eight-papers/LEAN_CORRESPONDENCE.md)列出各自的类型、前提和字段。固定比值实循环替代路线（ANISO-PSER F002）的实际终点是 [`IsingBulk.AnisoF002.full_uniform_field_conclusion`](lean/IsingBulk/AnisoF002/C03/FullUniformFieldConclusion.lean)。解析自然边界只要求耦合为正；实温度磁化率识别和能量场响应使用明示接口 `PublishedRealSpinFormFactors` 与 `PublishedRealGibbsFields`。见 [F002 范围与审计记录](docs/aniso-f002/PUBLICATION.md)及[八条路线状态](docs/eight-papers/EIGHT_PAPER_FORMALIZATION_STATUS.md)。双复变量端点/输运替代路线（JOINT-PSER）仍为 `NOT_SEPARATELY_FORMALIZED`。

[Lean 代码](lean/)增补了 F002；此前的证明源文件、工具链、锁定依赖和审计记录保留原字节。旧论文整树保存在[历史档案](archive/manuscripts/pre-eight-2026-10-30/README.md)，其中列有旧路径映射。原有固定提交和标签 URL 不变。

[构建与 CI 指南](docs/PROOF_CI_ROUTING.md)列出历史核验、独立重编译论文、F002 编译和内核重放命令。CI 只在稿件或稿件构建脚本变动时自动运行 TeX 构建；涉及 F002 的拉取请求运行其最终证明验收。

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
