# Ising 磁化率八篇论文

[当前八篇论文入口](papers/README.md) · [English](README.md) · [仓库地图](REPOSITORY_MAP.md)

四个主题各有两条不同的数学证明：低温磁化率、高温磁化率、固定比值各向异性磁化率，以及两个独立复耦合变量下的磁化率。入口列出八篇真实学术标题及 PDF/TeX；作者信息和论文内 ChatGPT 声明均保留。

原始固定比值证明在等耦合处合法调用原始低温、高温归一化自然边界定理；其实循环替代证明在文内独立处理等耦合情形。两篇双复变量证明各自证明联合结论、所有正比值切片及等耦合下降，未用环境空间非延拓代替切片证明。

六条路线的已完成 Lean 结果有[明确的类型、前提和字段范围](docs/eight-papers/LEAN_CORRESPONDENCE.md)。固定比值实循环替代路线仍为 PARTIAL；双复变量端点/输运替代路线仍为 NOT_SEPARATELY_FORMALIZED。[逐篇状态](docs/eight-papers/EIGHT_PAPER_FORMALIZATION_STATUS.md)和[对应矩阵](docs/eight-papers/SIX_PAPER_LEAN_SCOPE_MATRIX.csv)给出限定。

[Lean 代码](lean/)及锁定依赖保持原字节。旧论文整树保存在[次级历史档案](archive/manuscripts/pre-eight-2026-10-30/README.md)；原有固定提交和标签 URL 不变。移动 main 分支上的旧文件 URL 不会自动重定向。Lean 内冻结的技术说明及元数据保留旧路径，使用档案映射查阅。

运行 `python scripts/verify_eight_papers.py --historical-checks` 校验本次迁移及原验证器；运行 `python scripts/build_current_papers.py --output PATH` 在独立目录重编译当前八篇，不改动已发布稿件。

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
