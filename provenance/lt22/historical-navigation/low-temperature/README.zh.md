# 低温相自然边界证明

**有序纯相 · 无限正方晶格完整连通体磁化率**

这是仓库中的**低温相独立证明**，研究零外场、各向同性、无限二维正方晶格 Ising 模型在有序纯相中的连通响应。

令 (s=\sinh(2\beta J)>1)，(J>0)。归一化磁化率为
\[
\mathcal X_\mathrm{low}(s)=\sum_{(m,n)\in\mathbb Z^2}
\bigl(\langle\sigma_{00}\sigma_{mn}\rangle_{+}-M(s)^2\bigr),
\qquad M(s)^2=(1-s^{-4})^{1/4}.
\]
证明这一完整函数从物理低温解析芽延拓到 **(|s|>1)**，且 **(|s|=1) 的每一点**均构成自然边界。物理磁化率中的 (eta) 在相应局部温度分支上处理。

该成果包含**所有格点**与**完整无限偶粒子 form-factor 和**，先扣除自发磁化平方。当前对应论文 `v0.1-rc6`、Lean `v0.3.0-rc2`。

## 阅读低温相证明

| 内容 | 入口 |
|---|---|
| 当前数学手稿 | [PDF](../paper/next/manuscript.pdf) · [TeX](../paper/next/manuscript.tex) |
| Lean 独立入口 | [`IsingBulk.lean`](../lean/IsingBulk.lean) · [`Audit.lean`](../lean/Audit.lean) |
| 最终自然边界定理 | [低温相 Final 模块](../lean/IsingBulk/Final/) |
| 构建与验证 | [Lean 构建指南](../lean/README.md) · [版本记录](../docs/VERSIONS.md) |
| 数学范围 | [命题与量词](../CLAIMS.md) · [证明导读](../docs/PROOF_GUIDE.md) |
| 历史 | [发布记录](../RELEASE_NOTES.md) · [审计记录](../audits/README.md) |

低温相的证明、版本与审计有独立的冻结记录，不依赖高温相最终自然边界结论。

## 与高温相证明的关系

[高温相证明](../high-temperature/README.zh.md)研究**无序高温相的完整体磁化率**，对应**完整无限奇粒子级数**，从 **(|s|<1)** 的解析芽出发。两项成果仅共享底层 Lean 数学模块，不混同物理定义、最终定理和独立构建入口。

[English](README.md) · [仓库首页](../README.zh.md)
