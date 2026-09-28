# MR1 数学推导总索引与全部 25 节点

**结论层级：CLAIMED_TAIL_PROOF。** 本次相对于 E1、E2 的明确许可范围和一般数学，证明完整外部单值全纯性、正规收敛及完整 TAIL；E3 只在 P10 的有限 n<N0 部分使用。I3 未闭合，I6 只为条件推论，完整自然边界仍 unresolved。没有新增专用未证前提。

固定每一个允许 `(p,a,b)`，`N0=2p,k=N0²/2-1`。P08 的结论是

\[
\lim_{\varepsilon\downarrow0}\max_{0\le j\le k}
\varepsilon^{1/2}\sum_{\substack{N>N0\\N\ \mathrm{even}}}
|T_N^{(j)}((1+\varepsilon)s_*)|=0.
\]

所有常数可以依赖这一固定点及有限 k，不要求对所有素数统一；N、ε、λ 的其余量词及全部闭支撑包含列于 CONSTANTS.md。D0/R0 的归一化、导数意义和 BULK 的原点项没有改变。

## 文件阅读图

| 文件 | 本次推导内容 |
|---|---|
| P01_EXTERIOR_AND_NORMALIZATION.md | E1 角测度、留数、PAIR、原点/offsite、外部正规收敛 |
| P02_ARITHMETIC.md | 首次阶、所有阶的余弦对唯一、稠密性、非单位根、全部 N 的指数分离 |
| P03_CONTOURS_AND_DISCS.md | 实权重闭合同伦、完整 Jacobian/minor、Stokes 符号、消奇与三个不同参数盘 |
| P04_LARGE_ORDER_BUDGETS.md | F、较高阶、超高阶、大电流的完整匹配及阶乘预算 |
| P05_TRANSPORT_AND_FLUX.md | 全部高阶递推、系数与权重 jets、选中极点、hit-pair、全部前置通量 |
| P06_INTERMEDIATE_ALL_BRANCH.md | 中间阶 all-B 微核、全部符号远区、正负近碰撞的实际积分 |
| P07_MIXED_COMPACT_CURRENT.md | 真实标签覆盖、左/混合/全右、耦合电流、实差商及 coarea |
| P08_TAIL_SUMMATION_AND_SCOPE.md | 常数顺序、完整窗口求和与 I6 条件接口 |
| P09_BEARING_CHECKS.md | 解析负控制、方法修补、实际诊断及一般定理适用条件 |
| P10_FINITE_PARTICLE_INTERFACE.md | 已闭合的 E3 低粒子部分、有限首项模型尝试和精确未闭合 I3 |

上表路径均在 `proofs/`。COVERAGE.md 对 W1–W13 给出实际支撑、微分密度和归属；CONSTANTS.md 给出选取顺序和允许依赖。下面的每个节点都对应 OBLIGATIONS.json 的同一条记录。共享正文引理不被人为写成节点之间的循环。

## I1

**状态：proved。** 由 E1 的 Fredholm 角测度独立恢复双轮廓归一化，原点项为 1-M²、offsite 系数为 2T_N；重算 PAIR 与 R0。外部内根单值，紧集上 C^N N^(N/4)/N! 乘严格 n² 压缩给出偶数级数及任意固定阶导数的正规收敛。

本次证据：`proofs/P01_EXTERIOR_AND_NORMALIZATION.md` §P01.1；`proofs/P01_EXTERIOR_AND_NORMALIZATION.md` §P01.2；`proofs/P01_EXTERIOR_AND_NORMALIZATION.md` §P01.3；`proofs/P01_EXTERIOR_AND_NORMALIZATION.md` §P01.4。

数学依赖：无其他节点；见该正文内的直接推导。此节点直接使用的允许前提：E1、E2。

## I2

**状态：proved。** 对全部允许素数及 a,b 证明首次偶数阶 N0=2p、任意 Nickel 阶上无序余弦对唯一、点族稠密。迹证明 ξ 非单位根，整数范数给 A=(2p-3)log14 的全部正整数指数分离，不依赖有限枚举。

本次证据：`proofs/P02_ARITHMETIC.md` §P02.1；`proofs/P02_ARITHMETIC.md` §P02.2；`proofs/P02_ARITHMETIC.md` §P02.3；`proofs/P02_ARITHMETIC.md` §P02.4；`proofs/P02_ARITHMETIC.md` §P02.5。

数学依赖：I1。

## I3

**状态：unresolved。** E3 仅闭合 n<N0 的有限个偶数阶。已重算两个局部形式模型及其共同非零模型相位，但尚未证明合法实权重的平均角留数拼接、完整余项 √ε R^(k)→0、完整 T_N0 的 k 阶非零系数及 j<k 的有界性。因此不将 I3 默认为已证。

本次证据：`proofs/P10_FINITE_PARTICLE_INTERFACE.md` §P10.1；`proofs/P10_FINITE_PARTICLE_INTERFACE.md` §P10.2；`proofs/P10_FINITE_PARTICLE_INTERFACE.md` §P10.3；`proofs/P10_FINITE_PARTICLE_INTERFACE.md` §P10.4。

数学依赖：I1、I2。此节点直接使用的允许前提：E3。

## I4

**状态：proved。** 实际耦合权重上的同伦、三盘、固定 r/实域的任意 j≤k 微分以及全部前置通量闭合。混合活动平台精确保留耦合量；全紧致电流则用完整 logY/Σφ 梯度，不能偷用保持角和的场。

本次证据：`proofs/P03_CONTOURS_AND_DISCS.md` §P03.3；`proofs/P05_TRANSPORT_AND_FLUX.md` §P05.1；`proofs/P05_TRANSPORT_AND_FLUX.md` §P05.4；`proofs/P05_TRANSPORT_AND_FLUX.md` §P05.6；`proofs/P07_MIXED_COMPACT_CURRENT.md` §P07.5。

数学依赖：T1、T2、T3。

## I5

**状态：proved。** 对每个固定允许点证明 max_{0≤j≤k} √ε Σ_even N>N0 |T_N^(j)(sε)|→0。完整角域、全部尾 N 窗和所有导数已覆盖；不需要粒子项之间的抵消，也未假定 TAIL 或等强尾界。

本次证据：`proofs/P08_TAIL_SUMMATION_AND_SCOPE.md` §P08.1；`proofs/P08_TAIL_SUMMATION_AND_SCOPE.md` §P08.3；`proofs/P08_TAIL_SUMMATION_AND_SCOPE.md` §P08.4。

数学依赖：I1、I2、I4、T6。

## I6

**状态：conditional。** 若 I3 的完整首项 C_*≠0 及低导数估计成立，则 Leibniz 组合给出 Xcal^(k)=2M²(s*)C_* ε^-1/2+o(ε^-1/2)，再由稠密性、偶性与共轭性推出自然边界。I3 未闭合，所以本节点及自然边界不标 proved。

本次证据：`proofs/P08_TAIL_SUMMATION_AND_SCOPE.md` §P08.6；`proofs/P10_FINITE_PARTICLE_INTERFACE.md` §P10.4。

数学依赖：I1、I2、I3、I5。此节点直接使用的允许前提：E2。

## T1

**状态：proved。** 在无穿越的实际闭合同伦上，det M=∏d_i，命名电流替换列比值 2iτ，带权 Stokes 给出精确 F+K+S 及负号；所有 p,m,a 支撑平台均明确。根安全的基础不等式在同一引理直接证明，不与 T2 循环依赖。

本次证据：`proofs/P03_CONTOURS_AND_DISCS.md` §P03.1；`proofs/P03_CONTOURS_AND_DISCS.md` §P03.2；`proofs/P03_CONTOURS_AND_DISCS.md` §P03.3。

数学依赖：I1。

## T2

**状态：proved。** 给出双分支消奇、端点/互逆角完整 PAIR、三组严格余量、所有实际耦合参数的根与产品保护以及不含 P 的一体主函数。原 cε、F 的 c/N、大电流 cλ/N² 盘分别证明；允许紧致根在后两盘局部膨胀。

本次证据：`proofs/P03_CONTOURS_AND_DISCS.md` §P03.4；`proofs/P03_CONTOURS_AND_DISCS.md` §P03.5；`proofs/P03_CONTOURS_AND_DISCS.md` §P03.6；`proofs/P03_CONTOURS_AND_DISCS.md` §P03.7；`proofs/P03_CONTOURS_AND_DISCS.md` §P03.8。

数学依赖：T1。

## T3

**状态：proved。** all-B 的两个完整计数归纳、所有系数/散度/权重 jets、选中极点、hit-pair 计数和逐阶段通量均证明。P07 对混合测度与紧致实差商逐一验证同类传输的实际假设，而不是把它们当成未证类比。

本次证据：`proofs/P05_TRANSPORT_AND_FLUX.md` §P05.3；`proofs/P05_TRANSPORT_AND_FLUX.md` §P05.4；`proofs/P05_TRANSPORT_AND_FLUX.md` §P05.5；`proofs/P05_TRANSPORT_AND_FLUX.md` §P05.6；`proofs/P05_TRANSPORT_AND_FLUX.md` §P05.7；`proofs/P07_MIXED_COMPACT_CURRENT.md` §P07.2；`proofs/P07_MIXED_COMPACT_CURRENT.md` §P07.3；`proofs/P07_MIXED_COMPACT_CURRENT.md` §P07.4；`proofs/P07_MIXED_COMPACT_CURRENT.md` §P07.5。

数学依赖：T1、T2。

## T4

**状态：proved。** 超高阶双分支 L² 卷积、F 异常 Pfaffian 和完整匹配预算、较高阶高斯压缩及大电流的合法 Cauchy 全部闭合；包括 N!、余 Pfaffian、M_e√N 与 λ 积分成本。

本次证据：`proofs/P04_LARGE_ORDER_BUDGETS.md` §P04.1；`proofs/P04_LARGE_ORDER_BUDGETS.md` §P04.2；`proofs/P04_LARGE_ORDER_BUDGETS.md` §P04.3；`proofs/P04_LARGE_ORDER_BUDGETS.md` §P04.4。

数学依赖：W1、W2、W3、W13。

## T5

**状态：proved。** 中间阶微核、全部符号远区、正负近碰撞、左/混合/全右 K 与小电流覆盖齐全。真实实 Jacobian、像长、重数和所有成本给出 G_j(N,H)，C0 先于 B。

本次证据：`proofs/P06_INTERMEDIATE_ALL_BRANCH.md` §P06.3；`proofs/P06_INTERMEDIATE_ALL_BRANCH.md` §P06.5；`proofs/P06_INTERMEDIATE_ALL_BRANCH.md` §P06.7；`proofs/P07_MIXED_COMPACT_CURRENT.md` §P07.6。

数学依赖：W4、W5、W6、W7、W8、W9、W10、W11、W12。

## T6

**状态：proved。** COVERAGE 的每一项微分密度归属与精确分割、CONSTANTS 的无循环顺序和所有 N≥N0+2 的包含，合成全部 j≤k 的绝对尾和；不遗漏有限低尾阶或分窗等号。

本次证据：`proofs/P08_TAIL_SUMMATION_AND_SCOPE.md` §P08.2；`proofs/P08_TAIL_SUMMATION_AND_SCOPE.md` §P08.3。

数学依赖：T4、T5、I2、I4。

## W1

**状态：proved。** 超高阶原始完整角域；cε 盘、同半单位圆盘 z、Hy 的 (N-1)!! 完整匹配、双分支 L² 主函数与 N! 给出 [C(H+1)/√N]^N。

本次证据：`proofs/P04_LARGE_ORDER_BUDGETS.md` §P04.1。

实际覆盖：`COVERAGE.md` §W1。

数学依赖：T2。

## W2

**状态：proved。** 完整最终 F 的 p=1 锚点与 c/N 盘，保留紧致根膨胀 CM_e√N、异常子集展开、余 Pfaffian 及 N!；仅对完整 F 作 Cauchy。

本次证据：`proofs/P03_CONTOURS_AND_DISCS.md` §P03.7；`proofs/P04_LARGE_ORDER_BUDGETS.md` §P04.2。

实际覆盖：`COVERAGE.md` §W2。

数学依赖：T2。

## W3

**状态：proved。** 较高阶 K/小电流的原 cε 盘，扩大下支撑的 PAIR 高斯压缩，命名上方 q 独立 C^(N-1) 成本，完整 Jacobian 与非耦合 L¹ 主函数。

本次证据：`proofs/P04_LARGE_ORDER_BUDGETS.md` §P04.3。

实际覆盖：`COVERAGE.md` §W3。

数学依赖：T2。

## W4

**状态：proved。** all-B 微核及 jets；b_N 使 Y 由 ξ^N 分离，一相位场冻结 Z，第四象限锥、曲线长度与 dyadic 简单核积分给 b_N^((N²-1)/2)。

本次证据：`proofs/P06_INTERMEDIATE_ALL_BRANCH.md` §P06.2；`proofs/P06_INTERMEDIATE_ALL_BRANCH.md` §P06.3。

实际覆盖：`COVERAGE.md` §W4。

数学依赖：I2、T2、T3。

## W5

**状态：proved。** 微核补集锚点及全部 jets，ρ≥ρ_N；负锚点、跨符号和全非负逐一覆盖，全非负才用实际 min/max 的 coarea。分支尖端不假定全域凹性。

本次证据：`proofs/P06_INTERMEDIATE_ALL_BRANCH.md` §P06.4；`proofs/P06_INTERMEDIATE_ALL_BRANCH.md` §P06.5。

实际覆盖：`COVERAGE.md` §W5。

数学依赖：I2、T2、T3。

## W6

**状态：proved。** 近全碰撞包含使坐标同号并离单体分支；保留 e^(C0N³)，正区 Jac≥cNρ、负区用阻尼；L≥4N0+2，C0 在 B 前固定，不在 coarea 后再次积分半径。

本次证据：`proofs/P06_INTERMEDIATE_ALL_BRANCH.md` §P06.6；`proofs/P06_INTERMEDIATE_ALL_BRANCH.md` §P06.7。

实际覆盖：`COVERAGE.md` §W6。

数学依赖：I2、T2、T3。

## W7

**状态：proved。** K 的有效左标签提供固定 Z 间隙，允许其余分支；分支正则混合测度及补偿左角方向冻结 Y，按真实积分次序得到对数。

本次证据：`proofs/P07_MIXED_COMPACT_CURRENT.md` §P07.1；`proofs/P07_MIXED_COMPACT_CURRENT.md` §P07.2。

实际覆盖：`COVERAGE.md` §W7。

数学依赖：T2、T3。

## W8

**状态：proved。** K 无左但有分支：外锚点/内分支斜率分离，λ=0 双相位场及完整混合测度；负分支用阻尼，非负用 Jac≥c|b_j| 的实际 coarea。

本次证据：`proofs/P07_MIXED_COMPACT_CURRENT.md` §P07.1；`proofs/P07_MIXED_COMPACT_CURRENT.md` §P07.3。

实际覆盖：`COVERAGE.md` §W8。

数学依赖：T2、T3。

## W9

**状态：proved。** K 全紧致右域的真实曲率、差商、Δ(θ)^2 密度、选中通量和近/远 coarea；形状 ρ 与最大差分的 √N 损失明确计入。

本次证据：`proofs/P07_MIXED_COMPACT_CURRENT.md` §P07.4。

实际覆盖：`COVERAGE.md` §W9。

数学依赖：T2、T3。

## W10

**状态：proved。** 小电流存在左根时，原命名 q0 与分支平台精确保持耦合量，完整混合 Jacobian 保留；左根间隙控制 Z，Y 冻结并积分。

本次证据：`proofs/P07_MIXED_COMPACT_CURRENT.md` §P07.1；`proofs/P07_MIXED_COMPACT_CURRENT.md` §P07.2。

实际覆盖：`COVERAGE.md` §W10。

数学依赖：T2、T3。

## W11

**状态：proved。** 小电流混合区使用原命名 q0/真分支平台，任意阶段精确保持 P 及两个乘积；E=ε+λP/N 的真实正负分支几何和混合 coarea 给一致界。

本次证据：`proofs/P07_MIXED_COMPACT_CURRENT.md` §P07.3。

实际覆盖：`COVERAGE.md` §W11。

数学依赖：T2、T3。

## W12

**状态：proved。** 小电流全右域采用完整 logY 与 Σφ 梯度，不错误冻结 P。实光滑差商、耦合 Hessian 的 CN²(ε+λ) 扰动、Δ(θ)^2 及所有通量/coarea 重新核查。

本次证据：`proofs/P07_MIXED_COMPACT_CURRENT.md` §P07.5。

实际覆盖：`COVERAGE.md` §W12。

数学依赖：T2、T3。

## W13

**状态：proved。** 大电流 P≥1；cλ/N² 盘控制紧致根总膨胀与两个 λ 级乘积间隙，完整密度 Cauchy 后 λ 内取绝对值积分，得 C_j λ_*^(-j-1)。

本次证据：`proofs/P03_CONTOURS_AND_DISCS.md` §P03.8；`proofs/P04_LARGE_ORDER_BUDGETS.md` §P04.4。

实际覆盖：`COVERAGE.md` §W13。

数学依赖：T2。

## 证据声明的边界

这里的 proved 是本次数学重建的声明，不是行政工具的数学认证。符号计算只检验列出的代数恒等式，浮点诊断只适用于其实际有限配置。P10 的形式模型不进入任何 proved 尾项节点的依赖图；其完整局部化和余项估计未完成，已在 I3 明示。
