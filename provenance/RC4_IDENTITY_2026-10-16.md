# Ising rc4 文件身份与审计导航核查（2026-10-16）

核查基点：`e07ffa811e6661f932dda07ead5833b74853b1ac`。范围：两份指定 Drive PDF、完整 Git 历史中的论文差异、冻结记录、标签索引、仓库可见审计及公开引用导航。没有重做数学审计。

## 结论与后续基线

两份 PDF 是同一冻结数学候选的不同编辑构件。逐字节下载核验确认：10 月 8 日上传件等于 `v0.1-rc4` 标签中的 PDF；10 月 14 日上传件等于当前主分支 PDF。上传日期不是内容修订日期：后者在 10 月 4 日的 `a322ee43f8593a2fc5f9331f56a7052eb7f1dfe0` 已经进入仓库。

后续审计使用 **rc4 + 2026-10-04 bibliography/ORCID editorial revision**，并记录下表完整哈希、源码提交和配套索引。仅写“rc4 / 1 October 2026”不能唯一标识输入。历史 `v0.1-rc4` 标签及发布资产保留原身份，不移标签、不覆盖历史报告。

| 构件 | 标签原件 | 当前文献/ORCID修订件（后续基线） |
|---|---|---|
| Drive ID | `13kJcFtuB7KgDcSVZW0uAsPPxNi3WoyTf` | `1JgDFaBzg-QdZDVeCdxELNuEm4lIvezuw` |
| PDF bytes / pages | 325870 / 42 | 327486 / 42 |
| PDF SHA-256 | `624429bb0f2c211fec26cbc9e7608add65eb26a133a6af57259830b5fabd7693` | `107f09155e1ce46d65b5f8070ce33d3d9eddb177120413883d91b4f9c12202e4` |
| TeX SHA-256 | `2f3ad3af8b893e2387304a680dcf9cc5fa6b12a389e3ab7486e5c71512fd6235` | `6a1e5cfdc8681a6705d64dd648cbc33d46042c1f75aa624070ae1c4e125eaaf8` |
| LABEL_INDEX SHA-256 | `586aa17ed2db26f14d59a1587fac98fb1d1ac39b353d194dd9e4755071a4a896` | `a0be0b74df94a0f1908c492f120cd0f2b2405e3ebcdf68b09381580b8fe1f698` |

冻结数学候选由 [RC4_RELEASE_PREP_STATUS.json](../release/RC4_RELEASE_PREP_STATUS.json) 定位于 `59881ee24f43b8caab60f81ab3f87f758cfc03d5`；发布准备/标签解析至 `1b4b506c9cb19d5fdbf9f59d89c7a179739d337d`。前者、标签构件、后续编辑构件是三个不同概念。RELEASE_NOTES 中关于 rc3 冻结点 `813c6b9...` 的旧段落属于历史 rc3，不替代 rc4 的 W2/E1 记录。

## 数学内容是否变化

完整 TeX 差异只有三个插入块：作者 ORCID、引言中对 Boukraa 等 2007 文献及其证明范围的说明、新参考文献。删除这三个精确编辑插入后，整个 TeX 与标签原件逐字节一致；第 3 节至全部附录（参考文献前）的源文也逐字节一致。全部 65 个标签和编号一致。没有公式、定理、假设或证明改动。引言新增内容属于既有研究的归属/范围说明，不引入证明前提。

这与原有 [10 月 4 日维护记录](BIBLIOGRAPHY_ORCID_2026-10-04.json) 一致；本次独立复核了源差异和 PDF 字节身份，没有仅采用该记录的结论。

## 页码与参考文献迁移

不是整篇统一加一页。42 页总页数不变；65 个标签中 17 个页码增加一，48 个不变。页码指 PDF 内的印刷页码（本文件也等于从 1 开始的 PDF 页序）。

| 标签 | 编号 | 标签原件页码 | 当前页码 |
|---|---|---|---|
| `eq:roadmapfirst` | 1.1 | 2 | 3 |
| `eq:roadmaptail` | 1.2 | 2 | 3 |
| `eq:double` | 2.1 | 4 | 5 |
| `eq:bulk` | 2.2 | 4 | 5 |
| `lem:symmetry` | 2.2 | 5 | 6 |
| `lem:mean` | 4.1 | 7 | 8 |
| `thm:first` | 4.4 | 9 | 10 |
| `prop:selector` | 5.1 | 10 | 11 |
| `eq:FKS` | 5.2 | 10 | 11 |
| `eq:current` | 5.3 | 10 | 11 |
| `sec:K` | 7 | 13 | 14 |
| `lem:partition` | 7.1 | 13 | 14 |
| `sec:sectors` | 8 | 21 | 22 |
| `prop:mixed` | 8.1 | 21 | 22 |
| `eq:pullbackLie` | D.4 | 29 | 30 |
| `eq:weightjets` | D.7 | 30 | 31 |
| `app:auditmap` | G | 36 | 37 |

原有参考文献全部后移一位；新 `[1]` 为 `Boukraa2007`。应按作者/文献键核对，不能直接把旧 `[n]` 套到新 PDF。

| 文献键 | 原编号 | 当前编号 |
|---|---|---|
| `Boukraa2008` | 1 | 2 |
| `GuttmannEnting1996` | 2 | 3 |
| `McCoyMaillard2012` | 3 | 4 |
| `Nickel1999` | 4 | 5 |
| `Nickel2000` | 5 | 6 |
| `Orrick2001` | 6 | 7 |
| `PalmerTracy1981` | 7 | 8 |
| `TW2013` | 8 | 9 |
| `TW2014` | 9 | 10 |
| `TW2017Toeplitz` | 10 | 11 |
| `WMTB1976` | 11 | 12 |
| `Yang1952` | 12 | 13 |

## 现有审计和公开引用的实际影响

- `audits/views/` 的 16 份公开历史视图针对 v2–v8，`audits/README.md` 和 `VERSION_LEDGER.md` 已明确其历史输入边界。它们的 v7 第 16 页、附录 F 第 30–31 页等定位属于各自原稿；不是这两份 rc4 之间新增的引用错误。原文及结论均保留，不能把其页码改成 rc4 后再称原始审计。
- `provenance/source_coverage_v2.md` 是实际存在的旧导航问题：例如 `thm:first` 记为 4.4 / p.8，两个 rc4 分别为 p.9 / p.10；`thm:tail` 记为 9.1 / p.19，两个 rc4 均为 p.25。由此可知问题早于本次文献修订，不能全归因于这两份 PDF。已在该表前补历史范围说明；[机器记录](RC4_IDENTITY_2026-10-16.json) 给出其 76 次带标签定位的当前编号/页码。该对照仅提供导航，不扩大旧报告的输入范围。
- `docs/PROOF_GUIDE.md` 的 Theorem 4.4 p.10、9.1 p.25、9.2–9.3 p.26 与当前 PDF/索引一致。但原导航将 9.3 也称为 Theorem，实际为 Corollary；本次仅修正该名称。旧 PDF 的 4.4 位于 p.9；9.1–9.3 页码不变。`paper/LABEL_INDEX.json` 已在 10 月 4 日同步，无需重写。
- `CITATION.cff` 的 rc4 版本仍适用于冻结数学候选，但不能唯一标识 PDF；本次在论文入口和审计入口补充精确构件说明。外部文献自身的页码/公式引用不受本稿参考文献重新编号影响。
- 历史 rc4 release-prep 收据绑定旧 PDF 哈希，10 月 4 日收据绑定新哈希，均与实际文件吻合；不能拿历史收据中的 `current_sha256` 当作今日主分支身份。更晚 Lean v0.2.0/v0.2.1 的审计范围继续按其独立提交及收据判定，不因论文编辑修订自动扩大。

仓库可见记录没有显示某次审计因混用这两份 rc4 而得到错误数学结论。未提供的私下审计（例如其他会话中的整稿审计）无法从本仓库确认输入：要判定它实际用了哪份，只缺该次输入 PDF/TeX 或当时记录的 SHA-256；无需为此重做审计。本次公开引用检查限于仓库正文、导航、审计视图及元数据，不把它写成对所有外部转载的检索结论。

## 复核

[JSON 记录](RC4_IDENTITY_2026-10-16.json) 包含文件长度、SHA-256、Git blob、标签对象及解引用提交、完整页码/文献迁移、旧覆盖表的当前定位和历史视图哈希。

```sh
git rev-parse 'v0.1-rc4^{}'
git diff v0.1-rc4 e07ffa811e6661f932dda07ead5833b74853b1ac -- paper/manuscript.tex paper/LABEL_INDEX.json
git show v0.1-rc4:paper/manuscript.pdf > /tmp/ising-rc4-original.pdf
sha256sum /tmp/ising-rc4-original.pdf paper/manuscript.pdf paper/manuscript.tex paper/LABEL_INDEX.json
```

核查修订仅新增身份/对照说明和入口链接；不改论文 PDF/TeX、公式索引、冻结收据、标签、历史审计视图或数学证明。
