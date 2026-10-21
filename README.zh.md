# 二维正方晶格 Ising 体磁化率的自然边界

**两项独立证明 · 高温相与低温相 · 一套共享 Lean 数学基础**

本仓库收录针对**零外场、各向同性、无限二维正方晶格 Ising 模型完整体磁化率**的两项独立证明。它们分别从高温无序态与低温有序纯相出发，处理不同的完整 form-factor 级数，并各有独立的 Lean 定理和验证入口。

## 选择要阅读的证明

| **高温相：无序态磁化率** | **低温相：有序纯相连通磁化率** |
|---|---|
| **高温唯一 Gibbs 态的完整体磁化率** | **低温纯相的完整连通体磁化率** |
| 物理温度区间：`0 < s < 1` | 物理温度区间：`s > 1` |
| **完整无限奇粒子 form-factor 和** | **完整无限偶粒子 form-factor 和**，扣除自发磁化平方 |
| 从 `|s| < 1` 侧，证明单位圆每一点不可解析延拓 | 从 `|s| > 1` 侧，证明单位圆每一点不可解析延拓 |
| [**进入高温相证明 →**](high-temperature/README.zh.md) | [**进入低温相证明 →**](low-temperature/README.zh.md) |
| [数学论文](paper/ht/publication/manuscript.pdf) · [Lean 最终定理](lean/IsingBulk/HT/Final/PublishedPhysicalTheorem.lean) | [数学论文](paper/next/manuscript.pdf) · [Lean 证明入口](lean/IsingBulk.lean) |

其中 `s = sinh(2βJ)`、`J > 0`。**两项证明不是由对方的结论直接推出的。** 它们分别证明对应物理解析芽的完整无限粒子和存在不可相消的自然边界。

## 仓库结构

| 阅读入口 | 内容 |
|---|---|
| [**高温相证明**](high-temperature/README.zh.md) | 完整定理、数学手稿、Lean 源码、复现与独立审计 |
| [**低温相证明**](low-temperature/README.zh.md) | 完整定理、数学手稿、Lean 源码、复现与历史版本 |
| [**共享 Lean 数学模块**](lean/IsingBulk/) | 两项工作复用的分析、代数、轮廓积分与求和引理，不复制第二套 LT 数学库 |
| [**源码及证明分区说明**](REPOSITORY_MAP.md) | 模块归属、冻结源码身份与分开的构建入口 |

顶层的“高温相／低温相”目录主要负责清晰导航，原 Lean 模块路径保留冻结审计版本。低温相的独立构建入口为 `lean/IsingBulk.lean`、`lean/lakefile.toml`；高温相为 `lean/IsingBulkHT.lean`、`lean/lakefile.ht.toml`。高温证明复用底层数学引理，但不调用低温的最终自然边界定理。

### 形式化及审计状态

- **低温相：**数学稿 `v0.1-rc6`，Lean `v0.3.0-rc2`；对应历史版本、验证记录及发布信息保留。
- **高温相：**数学稿 `HT-1.0`，Lean 冻结版 `1747`；已通过干净构建、官方 fresh 内核重放，以及独立 Pro/Codex 敌对性审计（均为 `EXHAUSTED`）。物理解析芽定理显式使用已发表的实温度完整体磁化率 form-factor 公式。
- 目前没有独立人类同行评审结果；每项研究的数学范围、物理输入、审计与来源记录分别保存。

建议从各自的相别入口开始阅读和复现，不必一次构建两项研究。原有 LT 历史标签、发行附件和源码路径不会因整合而改写。

[**English**](README.md) · [作者及来源](AUTHORSHIP.md) · [代码许可 MIT](LICENSE) · [文档许可 CC BY 4.0](LICENSE-DOCUMENTATION.md)

两项结果请分别引用：[高温相](high-temperature/CITATION.cff) · [低温相](low-temperature/CITATION.cff)。[高温冻结稿件](paper/ht/frozen/manuscript.pdf)与[出版版编辑记录](paper/ht/publication/README.md)分别保留。
