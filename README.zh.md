# 二维正方晶格 Ising 体磁化率的自然边界

本仓库展示无限正方晶格 Ising 模型**零外场完整体磁化率**的四项数学研究及相应的 Lean 形式化：各向同性低温和高温的独立证明、任意固定正耦合比的各向异性结果，以及两个独立复耦合变量下的母定理。

**首次阅读建议从四份完整 Reader 易读版开始。** 它们已经接受独立的编辑保真和 Lean 对应审查；原始数学命题、假设和证明机制保持不变，原稿及对应源码仍可用于精确核对。

## 四篇论文

| 数学成果 | 推荐阅读 | 数学原稿 | Lean 形式化 |
|---|---|---|---|
| **两个独立复耦合的联合自然边界** | [Reader PDF](paper/joint/reader/manuscript.pdf) · [TeX](paper/joint/reader/manuscript.tex) | [原始数学稿](paper/joint/frozen/manuscript.pdf) | [Lean 定理](lean/IsingBulk/Joint/Final/FullConclusion.lean) |
| **固定正耦合比的各向异性自然边界** | [Reader PDF](paper/aniso/reader/manuscript.pdf) · [TeX](paper/aniso/reader/manuscript.tex) | [原始数学稿](paper/aniso/frozen/manuscript.pdf) | [Lean 定理](lean/IsingBulk/Anisotropic/Final/FullTheorem.lean) |
| **各向同性高温体磁化率** | [Reader PDF](paper/ht/reader/manuscript.pdf) · [TeX](paper/ht/reader/manuscript.tex) | [原始数学稿](paper/ht/frozen/manuscript.pdf) | [Lean 定理](lean/IsingBulk/HT/Final/PublishedPhysicalTheorem.lean) |
| **各向同性低温连通体磁化率** | [Reader PDF](paper/lt/reader/manuscript.pdf) · [TeX](paper/lt/reader/manuscript.tex) | [原始数学稿](paper/next/manuscript.pdf) | [Lean 定理](lean/IsingBulk/Final/UnconditionalNaturalBoundary.lean) |

## 四项结果的范围

### 两个独立复耦合的联合自然边界

双复变量母定理处理完整高低温体磁化率、正耦合比切片、各向同性特化和定量边界障碍，明确列出共同的实物理前提。

[成果说明](joint/README.zh.md) · [构建与验证](docs/joint/BUILD_AND_VERIFY.md) · [引用](joint/CITATION.cff)

### 固定正耦合比的各向异性自然边界

对任意固定有限正耦合比，完整高低温体磁化率在相应透镜域和上图域具有自然边界，并严格区分两侧的场导数及物理前提。

[成果说明](anisotropic/README.zh.md) · [构建与验证](docs/aniso/BUILD_AND_VERIFY.md) · [引用](anisotropic/CITATION.cff)

### 各向同性高温体磁化率

无序相定理覆盖完整奇粒子展开、同点项和全部格点，以单位圆为自然边界；已发表的实温角积分表示是明确的物理前提。

[成果说明](high-temperature/README.zh.md) · [构建与验证](docs/ht/BUILD_AND_VERIFY.md) · [引用](high-temperature/CITATION.cff)

### 各向同性低温连通体磁化率

有序纯相定理覆盖全部格点与完整正偶粒子展开，扣除自发磁化平方，并保留独立原始证明与物理接口。

[成果说明](low-temperature/README.zh.md) · [构建与验证](lean/README.md) · [引用](low-temperature/CITATION.cff)

## 数学关系、版本与复现

双复变量母定理通过内部论证回收固定正耦合比与各向同性特化结论；固定耦合比结果覆盖两相，而较早的高温与低温独立证明及各自物理对象仍完整保留。

各向同性变量为 s = sinh(2βJ)；各向异性先固定耦合比，再对 z = 2βJ 作复延拓。外部物理关联函数及 Gibbs 场前提、仅在自然语言论文中给出的更精细结论，均在各篇的对应文档中独立标明，不被混称为逐字形式化的 Lean 导出定理。

**Reader 易读版**是独立核查过的完整行文改善稿；**原始/冻结版**是精确数学基准；较早的 **publication 署名版**有些只修改作者和日期元数据。C001、C002、HT-1.0 等内部标识保留在[版本记录](docs/VERSIONS.md)，不作为论文正式名称。

[论文版本目录](paper/README.md) · [仓库与定理对应](REPOSITORY_MAP.md) · [English](README.md) · [作者与来源](AUTHORSHIP.md) · [MIT 源码许可](LICENSE) · [CC BY 4.0 文档许可](LICENSE-DOCUMENTATION.md)
