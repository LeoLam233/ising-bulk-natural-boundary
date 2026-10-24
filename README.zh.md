# 正方晶格 Ising 体磁化率的自然边界

**三个研究结果 · 各自的物理对象与 Lean 终点 · 共享形式数学库**

本仓库分别展示各向同性低温、各向同性高温，以及固定耦合比各向异性模型的完整体磁化率结果。每个结果保留独立论文、物理前提、引用信息与构建入口。

- **ANISO C001：**[论文](paper/aniso/publication/manuscript.pdf) · [Lean 终点](lean/IsingBulk/Anisotropic/Final/FullTheorem.lean) · [构建](docs/aniso/BUILD_AND_VERIFY.md) · [引用](anisotropic/CITATION.cff)。
- **各向同性 HT：**[论文](paper/ht/publication/manuscript.pdf) · [Lean 终点](lean/IsingBulk/HT/Final/PublishedPhysicalTheorem.lean) · [构建](docs/ht/BUILD_AND_VERIFY.md) · [引用](high-temperature/CITATION.cff)。
- **各向同性 LT：**[论文](paper/next/manuscript.pdf) · [Lean 终点](lean/IsingBulk/Final/UnconditionalNaturalBoundary.lean) · [构建](lean/README.md) · [引用](low-temperature/CITATION.cff)。

## 固定耦合比各向异性结果 — ANISO C001

覆盖任意有限 `J > 0`、`lam > 0`、所有晶格位点和全部无限奇/偶粒子阶。自然边界覆盖高温透镜域和低温右侧上图域边界的每个有限点，同时给出高温双侧及低温正相右侧零场响应。显式的实温自旋与 Gibbs 场前提见[物理接口](docs/aniso/PHYSICAL_INPUTS.md)。

[ANISO 入口](anisotropic/README.zh.md) · [论文](paper/aniso/publication/manuscript.pdf) · [Lean：`IsingBulk.Anisotropic.full_uniform_field_conclusion`](lean/IsingBulk/Anisotropic/Final/FullTheorem.lean) · [构建](docs/aniso/BUILD_AND_VERIFY.md) · [引用](anisotropic/CITATION.cff)

## 各向同性高温结果 — HT-1.0 / Lean 1747

`0 < s < 1` 的无序相完整体磁化率，包含全部奇粒子阶，从单位圆内部逼近。物理解析芽定理显式使用已发表的实温全体角积分表示。

[高温入口](high-temperature/README.zh.md) · [论文](paper/ht/publication/manuscript.pdf) · [Lean：`IsingBulk.HT.Final.publishedPhysicalSusceptibility_germ_natural_boundary`](lean/IsingBulk/HT/Final/PublishedPhysicalTheorem.lean) · [构建](docs/ht/BUILD_AND_VERIFY.md) · [引用](high-temperature/CITATION.cff)

## 各向同性低温结果 — 论文 v0.1-rc6 / Lean v0.3.0-rc2

`s > 1` 的有序纯相连通体磁化率，在全晶格求和中减去自发磁化平方，包含全部正偶粒子阶，从单位圆外部逼近。物理识别保留已记录的 E1/E2 接口。

[低温入口](low-temperature/README.zh.md) · [论文](paper/next/manuscript.pdf) · [Lean：`IsingBulk.Final.theorem_nb_physical`](lean/IsingBulk/Final/UnconditionalNaturalBoundary.lean) · [构建](lean/README.md) · [引用](low-temperature/CITATION.cff)

各向同性变量为 `s = sinh(2βJ)`；ANISO 在固定耦合比后对 `z = 2βJ` 作复延拓。[仓库地图](REPOSITORY_MAP.md)和[版本索引](docs/VERSIONS.md)区分共享数学、冻结源码与出版版本，已有 LT/HT 路径、发布和历史记录均保留。

ANISO 的[38 页冻结审计版](paper/aniso/frozen/manuscript.pdf)和[单独的 39 页研究原稿](paper/aniso/research-original/manuscript.pdf)分别保存；初次署名出版版仅修改导言区元数据。[后续三篇读者版编辑](docs/aniso/EDITORIAL_FOLLOWUP_SCOPE.md)属于独立 PR。[审计来源](docs/aniso/AUDIT_EVIDENCE.md)区分历史调查结果与本次实际执行的发布验证。

[English](README.md) · [作者与来源](AUTHORSHIP.md) · [MIT 代码许可](LICENSE) · [CC BY 4.0 作者文档许可](LICENSE-DOCUMENTATION.md)
