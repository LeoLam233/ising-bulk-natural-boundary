# 固定耦合比各向异性 Ising 体磁化率

**ANISO C001 · 任意有限正耦合比 · 高温与低温两侧**

取水平耦合 `J > 0`、固定垂直/水平耦合比 `lam > 0`。本结果研究无限正方晶格的完整体磁化率：高温包含全部无限奇粒子阶；低温采用正相的连通磁化率，在全晶格求和内减去自发磁化平方，包含全部正偶粒子阶。所有晶格位点均保留。

[阅读论文](../paper/aniso/publication/manuscript.pdf) · [Lean 最终定理](../lean/IsingBulk/Anisotropic/Final/FullTheorem.lean) · [构建与验证](../docs/aniso/BUILD_AND_VERIFY.md) · [本结果的引用](CITATION.cff) · [English](README.md)

令 `z = 2βJ`。高温复域为有界透镜域，低温复域为右侧上图域。完整归一化协方差和及其能量场归一化在对应域内解析，并在对应边界的每个有限点阻止局部解析延拓。`lam = 1` 通过完整级数的精确对应使用已有 LT/HT 定理。

终点为 `IsingBulk.Anisotropic.full_uniform_field_conclusion`，同时包含全位点可求和性、物理磁化率识别、高温零场双侧导数、低温正相零场右导数。显式物理前提为 `PublishedRealSpinFormFactors` 和 `PublishedRealGibbsFields`；[物理接口说明](../docs/aniso/PHYSICAL_INPUTS.md) 完整列出这些前提，区分所提供的实温 Gibbs 数据与 Lean 内部推导。

[定理类型与证明路线](../docs/aniso/PROOF_MAP.md) · [论文版本](../paper/aniso/README.md) · [源码身份与哈希](../docs/aniso/VERSION_IDENTITY.md) · [审计证据来源](../docs/aniso/AUDIT_EVIDENCE.md)

762 个 ANISO 模块、两个冻结入口及新增 Lake 配置均逐字节来自用户提供的 C001 内层归档。38 页数学审计版和单独的 39 页研究原稿分别保存；本次署名出版版仅修改导言区和元数据。三篇论文的后续行文编辑属于另一个独立 PR。

作者：**Dehao Lin**，中山大学物理学院；[ORCID 0009-0001-4551-8490](https://orcid.org/0009-0001-4551-8490)；lindh9@mail2.sysu.edu.cn。代码采用 [MIT](../LICENSE)，作者文档采用 [CC BY 4.0](../LICENSE-DOCUMENTATION.md)。
