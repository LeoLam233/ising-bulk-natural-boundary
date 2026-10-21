# 高温相自然边界证明

**无序高温相 · 无限正方晶格完整体磁化率**

这是仓库中的**高温相独立证明**，研究零外场、各向同性、无限二维正方晶格 Ising 模型。

令 (s=\sinh(2\beta J))，(J>0)。从物理高温区间 (0<s<1) 出发，证明完整磁化率解析芽在 **(|s|<1)** 上全纯，并以 **(|s|=1) 的每一点**为自然边界。

研究对象包含**全部格点**和**完整无限奇粒子 form-factor 级数**，并保留物理磁化率的逆温度因子 (eta)。唯一外部物理接口是已发表的实温度精确角积分表示；复杂轮廓、无限尾项的非相消及自然边界结论由 Lean 内部证明。

## 阅读高温相证明

| 内容 | 入口 |
|---|---|
| 数学论文（冻结审计稿） | [PDF](../paper/ht/frozen/manuscript.pdf) · [TeX](../paper/ht/frozen/manuscript.tex) |
| Lean 源码 | [高温相证明模块](../lean/IsingBulk/HT/) |
| **最终 Lean 定理** | [`publishedPhysicalSusceptibility_germ_natural_boundary`](../lean/IsingBulk/HT/Final/PublishedPhysicalTheorem.lean) |
| 独立构建与验证入口 | [`IsingBulkHT.lean`](../lean/IsingBulkHT.lean) · [`AuditHT.lean`](../lean/AuditHT.lean) |
| 数学—Lean 对应 | [证明导读](../docs/ht/PROOF_MAP.md) · [复现命令](../docs/ht/BUILD_AND_VERIFY.md) |
| 审计状态和定理范围 | [验证说明](../docs/ht/README.md) |

冻结版本 `HT-1.0 / Lean 1747` 已通过干净构建、官方 fresh 内核重放，以及独立 Pro、Codex 敌对性审计（均为 `EXHAUSTED`）。这些 AI 审计不是人类同行评审。

## 与低温相证明的关系

[低温相证明](../low-temperature/README.zh.md)研究的是**有序纯相的连通体磁化率**，对应**完整无限偶粒子级数**。高温相证明不由低温相结论通过对偶性直接得到；两项成果共享底层数学引理，但拥有不同的最终定理和构建入口。

[English](README.md) · [仓库首页](../README.zh.md)

## 署名出版版与引用

本结果的[署名出版版 PDF](../paper/ht/publication/manuscript.pdf)和
[TeX](../paper/ht/publication/manuscript.tex)仅编辑作者、联系信息及版本日期。
[审计冻结版](../paper/ht/frozen/manuscript.pdf)保持不变；数学正文逐字节相同，
详见[编辑身份记录](../paper/ht/publication/README.md)。
请分别引用[高温相结果](CITATION.cff)与[低温相结果](../low-temperature/CITATION.cff)。
新增 Lean 代码采用 [MIT](../LICENSE)，作者创作的稿件与文档采用
[CC BY 4.0](../LICENSE-DOCUMENTATION.md)。

[Publication identities, exact verification and independent audit attachments](PUBLICATION.md).
