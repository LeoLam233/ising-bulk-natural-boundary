# 原始证明链与修订稿的覆盖映射

本文以原 v38 的最终第二族主链及上一版活跃闭包为基线，回查最终目标、支持矩阵与关键替代路线。40 个核心文件和 1 个辅助记录全部列在下表。文件被映射到正文，不等于文件内所有历史主张都正确，也不等于全部证明已经通过独立审计。

正文的 13 个区域覆盖表见 Appendix G；精确行号、公式编号与页码见 LABEL_INDEX.json。新增递推和圆盘保护推导也属于待审查的候选论证。

| v38 文件 | 在本稿中的位置 | 来源角色 |
|---|---|---|
| `ALL_B_LIE_NUMERATOR_DESOURCE.md` | C8: `lem:lie`（D.1, p. 21）<br>C11: `lem:branch`（7.4, p. 13）<br>C13: `prop:allB`（7.6, p. 14）<br>REG: `eq:branchregular`（D.2, p. 22）<br>C8J: `lem:jets`（D.2, p. 23） | 正文推导或接口的来源；原笔记中的通过判断不是证据 |
| `COMPACT_AMPLITUDE_MCCOY_CROSSCHECK.md` | B5: `app:normalization`（F, p. 27） | 幅值比较；不作为本稿归一化公理 |
| `COMPACT_FOUR_CHART_NORMALIZATION_RESOLUTION.md` | B5: `app:normalization`（F, p. 27） | 正文推导或接口的来源；原笔记中的通过判断不是证据 |
| `COMPACT_PRIME_MEAN_RESIDUE_AMPLITUDE.md` | B1: `lem:mean`（4.1, p. 6）<br>B2: `lem:period`（4.2, p. 7）<br>B3: `lem:complement`（4.3, p. 7）<br>B4: `thm:first`（4.4, p. 8） | 正文推导或接口的来源；原笔记中的通过判断不是证据 |
| `COMPACT_R_FRESH_KTH_COAREA_PROOF.md` | C10: `prop:compactR`（8.2, p. 16） | 正文推导或接口的来源；原笔记中的通过判断不是证据 |
| `COMPACT_R_RATIONAL_ATLAS_PROOF.md` | C10: `prop:compactR`（8.2, p. 16） | 正文推导或接口的来源；原笔记中的通过判断不是证据 |
| `COMPACT_R_STOKES_EQUALITY_DESOURCE.md` | C10: `prop:compactR`（8.2, p. 16） | 正文推导或接口的来源；原笔记中的通过判断不是证据 |
| `FINAL_KILL_AUDIT_v1.md` | D1: `thm:conditional`（9.2, p. 19）<br>D2: `thm:nb`（9.3, p. 19） | 最终目标与接口记录；其审计结论不作为证明 |
| `FORM_FACTOR_NORMALIZATION_AUDIT.md` | R1: `sec:setup`（2, p. 3） | 正文推导或接口的来源；原笔记中的通过判断不是证据 |
| `FORM_FACTOR_SIGN_SYMMETRY.md` | A4: `lem:symmetry`（2.2, p. 5） | 正文推导或接口的来源；原笔记中的通过判断不是证据 |
| `GENERIC_BRANCH_REAL_PHASE_GEOMETRY.md` | C11: `lem:branch`（7.4, p. 13） | 正文推导或接口的来源；原笔记中的通过判断不是证据 |
| `GENERIC_K_PAIR_COMPACTNESS.md` | C4: `lem:contraction`（7.2, p. 12） | 正文推导或接口的来源；原笔记中的通过判断不是证据 |
| `GENERIC_MIXED_STOKES_REDERIVATION.md` | C9: `prop:mixed`（8.1, p. 15） | 正文推导或接口的来源；原笔记中的通过判断不是证据 |
| `GENERIC_PAIR_TAIL.md` | C1: `prop:ultrahigh`（5.2, p. 9） | 正文推导或接口的来源；原笔记中的通过判断不是证据 |
| `GENERIC_UPPER_ANCHOR_AUDIT.md` | C2: `prop:selector`（5.1, p. 8）<br>C5: `prop:F`（6.1, p. 10） | 正文推导或接口的来源；原笔记中的通过判断不是证据 |
| `GLOBAL_DEFORMATION.md` | C2: `prop:selector`（5.1, p. 8） | 正文推导或接口的来源；原笔记中的通过判断不是证据 |
| `GLOBAL_PAIR_CONSTANTS_INTERFACE.md` | C4: `lem:contraction`（7.2, p. 12）<br>C4D: `lem:originaldisk`（7.3, p. 12） | 正文推导或接口的来源；原笔记中的通过判断不是证据 |
| `L2_PAIR_TAIL.md` | C0: `lem:schur`（C.1, p. 21）<br>C1: `prop:ultrahigh`（5.2, p. 9） | 正文推导或接口的来源；原笔记中的通过判断不是证据 |
| `LARGE_LAMBDA_COMPLEX_DISK_AUDIT.md` | C6: `prop:largeS`（8.4, p. 18）<br>C6G: `lem:protected`（8.3, p. 17） | 正文推导或接口的来源；原笔记中的通过判断不是证据 |
| `LIE_POLE_FILTRATION_PROOF.md` | C8: `lem:lie`（D.1, p. 21）<br>C8J: `lem:jets`（D.2, p. 23） | 正文推导或接口的来源；原笔记中的通过判断不是证据 |
| `NESTED_ANGULAR_PARTITION.md` | C3: `lem:partition`（7.1, p. 11）<br>C9: `prop:mixed`（8.1, p. 15） | 正文推导或接口的来源；原笔记中的通过判断不是证据 |
| `NONRESONANT_BRANCH_EXPONENTIAL_CUTOFF.md` | A3: `lem:resultant`（3.2, p. 5）<br>C12: `prop:micro`（7.5, p. 14） | 正文推导或接口的来源；原笔记中的通过判断不是证据 |
| `NONRESONANT_BRANCH_HOSTILE_AUDIT.md` | C12: `prop:micro`（7.5, p. 14）<br>C13: `prop:allB`（7.6, p. 14） | 正文推导或接口的来源；原笔记中的通过判断不是证据 |
| `ONSITE_GROUPING_EXACT_AUDIT.md` | R1: `sec:setup`（2, p. 3）<br>B5: `app:normalization`（F, p. 27） | 正文推导或接口的来源；原笔记中的通过判断不是证据 |
| `ORIGINAL_CONTOUR_TWO_PHASE_FIELD.md` | C8: `lem:lie`（D.1, p. 21）<br>C8J: `lem:jets`（D.2, p. 23） | 正文推导或接口的来源；原笔记中的通过判断不是证据 |
| `PAIR_COMPACTNESS_ENDPOINT_EQUALITY_AUDIT.md` | C4: `lem:contraction`（7.2, p. 12） | 正文推导或接口的来源；原笔记中的通过判断不是证据 |
| `PAIR_CONSTANTS_COMPLEX_DISK_FRESH_AUDIT.md` | C4: `lem:contraction`（7.2, p. 12）<br>C6: `prop:largeS`（8.4, p. 18）<br>C4D: `lem:originaldisk`（7.3, p. 12）<br>C6G: `lem:protected`（8.3, p. 17） | 正文推导或接口的来源；原笔记中的通过判断不是证据 |
| `PFAFFIAN_TAIL.md` | C0: `lem:schur`（C.1, p. 21）<br>R3: `app:pfaffian`（C, p. 21）<br>C1: `prop:ultrahigh`（5.2, p. 9） | 正文推导或接口的来源；原笔记中的通过判断不是证据 |
| `RESIDUE_REDUCTION.md` | R2: `lem:residue`（2.1, p. 4）<br>R3: `app:pfaffian`（C, p. 21）<br>REG: `eq:branchregular`（D.2, p. 22） | 正文推导或接口的来源；原笔记中的通过判断不是证据 |
| `SECOND_FAMILY_BULK_NATURAL_BOUNDARY_CANDIDATE.md` | C14: `thm:tail`（9.1, p. 19）<br>D1: `thm:conditional`（9.2, p. 19）<br>D2: `thm:nb`（9.3, p. 19） | 正文推导或接口的来源；原笔记中的通过判断不是证据 |
| `SECOND_FAMILY_DESOURCE_SUPPORT_MATRIX.md` | C3: `lem:partition`（7.1, p. 11） | 正文推导或接口的来源；原笔记中的通过判断不是证据 |
| `SECOND_FAMILY_KILL_PHASE_LOG.md` | Appendix G.5 / 历史支持记录 | 保留为历史记录，不作为证明前提 |
| `SECOND_FAMILY_TAIL_GLOBAL_JET_AUDIT.md` | C3: `lem:partition`（7.1, p. 11）<br>C7: `prop:highKS`（8.5, p. 18）<br>C8: `lem:lie`（D.1, p. 21）<br>C14: `thm:tail`（9.1, p. 19）<br>C8J: `lem:jets`（D.2, p. 23） | 正文推导或接口的来源；原笔记中的通过判断不是证据 |
| `SMALL_LAMBDA_LIE_ATLAS_AUDIT.md` | C7: `prop:highKS`（8.5, p. 18）<br>C9: `prop:mixed`（8.1, p. 15） | 正文推导或接口的来源；原笔记中的通过判断不是证据 |
| `STOKES_TOP_FORM_ORIENTATION_REDERIVATION.md` | C2: `prop:selector`（5.1, p. 8） | 正文推导或接口的来源；原笔记中的通过判断不是证据 |
| `TAIL_COMPOSITION_HOSTILE_AUDIT.md` | C14: `thm:tail`（9.1, p. 19） | 正文推导或接口的来源；原笔记中的通过判断不是证据 |
| `TWO_NONZERO_G3_FRESH_COAREA_PROOF.md` | C12: `prop:micro`（7.5, p. 14）<br>C13: `prop:allB`（7.6, p. 14） | 正文推导或接口的来源；原笔记中的通过判断不是证据 |
| `TWO_NONZERO_PRIME_FAMILY.md` | A1: `lem:cyclotomic`（A.1, p. 20）<br>A2: `thm:prime`（3.1, p. 5）<br>A3: `lem:resultant`（3.2, p. 5）<br>A4: `lem:symmetry`（2.2, p. 5） | 正文推导或接口的来源；原笔记中的通过判断不是证据 |
| `UPPER_CUTOFF_STOKES_RETRACTION.md` | C2: `prop:selector`（5.1, p. 8） | 正文推导或接口的来源；原笔记中的通过判断不是证据 |
| `UPPER_SELECTED_MATCHING_FRESH_RECONSTRUCTION.md` | C5: `prop:F`（6.1, p. 10） | 正文推导或接口的来源；原笔记中的通过判断不是证据 |
| `UPPER_SELECTED_MATCHING_RECHECK.md` | C5: `prop:F`（6.1, p. 10） | 正文推导或接口的来源；原笔记中的通过判断不是证据 |

## 历史路线的处理

下列旧问题没有通过删去目标来规避；本文使用 v38 中已经存在的替代路线，并将需要审查的接口展开。

| 旧路线或问题 | 本稿实际使用的替代 |
|---|---|
| 在首个奇异阶上使用尾项 coarea | 首阶实际均值留数与 beta 形状积分；coarea 仅用于 N >= N0+2 |
| 联合均值/形状绝对极限 | 先在有限物理矩形上取均值留数，再作形状极限 |
| 除回原 Vandermonde 后声称只有一个碰撞极点 | 未因式除去的分子递推，Appendix D.3–D.4 |
| 全部根在放大的复圆盘上仍在单位圆内 | 分开分支保护、紧根膨胀和所选根对全局乘积的控制 |
| 紧组包含精确分支导致严格 pair 常数失败 | 先固定分支/紧组间隔，再选择松弛量、端点切片与变形强度 |
| 中央连接轮廓、共振分支或退化四粒子端点幅值 | 非共振第二族、resultant 间隔、指数微核与锚点补集；不依赖旧路线 |
| 微分会击穿支持条件 | 固定嵌套光滑分割，所有有限 jet 保留命名锚点和 plateau |
| exp(C N^3) 被错误视为多项式 | 保留真实代价，先定其系数，再选 rho_N = exp(-B N) |

完整的旧路线分类保存在输入重构包中，其分类是历史元数据，不是本次重新认证。原始 v38 的全部 192 个成员均保存在本包 inputs 下的原始 ZIP 中，并按原 SHA256 清单逐项验证。
