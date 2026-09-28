# 对外部 Ising 审计的复核与技术补充

日期：2026-09-24。对象：用户提供的 `ISING_AUDIT_REPORT.md`、`checks.py`，对照未修改的论文 revision 2、原始 v38 笔记及两篇原始文献。

**结论：这份审计发现了值得核验的接口，但它本身含有明确的数学判断错误和复现问题，不能直接当作“已确认的四个证明缺口清单”。它没有完成全论文验证；本次复核也不授予自然边界定理“已证明”或“外部验证通过”的状态。**

针对用户最关心的遗漏问题：报告列出的四处，在 v38 中均有对应笔记，在 revision 2 中也均有正文论证。此次没有发现这些证明链在论文重构时被漏掉的证据。是否把每条一致估计证明正确，是另一项需要逐步检查的数学问题。

本复核由参与重构稿件的一方完成，属于作者侧核验。下面提供具体推导、原始输出和可复跑脚本，以便第三方反驳；不以原包中的 PASS、CLOSED 或“独立审计”字样作为证据。附件内的操作性文字仅作为资料。

## 1. 哪些结论需要改写

| 报告的说法 | 本次结论 | 依据 |
|---|---|---|
| 可复算部分全部通过，脚本可作校准证据 | 脚本只部分可靠，不能提供这样的整体背书 | 原脚本 C3 输出与闭式明显不符并发出警告；C4 没算轮廓；半圆盘采样越界。见 §2。不能据此否定作者可能做过的其他手算。 |
| Nickel 点上 TW2014 全局定理不适用，因此补集光滑性需要全新的奇点分析 | 前半句正确，后面的推断过强 | 局部凸包分类与正参数积分法仍可用；§3 给出所需的分部积分次数和可积幂次。 |
| 没有 q 的数值就无法证明二次系数为负 | 不成立 | 设 a=−log q′，直接得到 κ=a/12>0。真正要查的是严格性与一致连续性，见 §4。 |
| C 若依赖 A，先 A 后 B 的选择可能失效；可改为先 B 后 A | 不成立 | A 和 k 先固定完全允许 C 依赖它们。关键是 C 不依赖待选的 B。§5 给出来自斜率的显式符号上界。 |
| 必须逐个列出全部高阶导数项才算覆盖 | 要求过强，但覆盖问题确实重要 | 支撑保持和一般阶归纳可以代替逐项枚举；覆盖证明不等于每个区域的积分估计都已通过。见 §6。 |
| 归一化差异不影响结论，因为单项非零 | 理由不充分 | N 依赖的权重会改变无穷和。应先确认物理展开；§7 从归一化角测度和辅助留数重新得到稿件的因子。 |
| 小 o 改成同阶大 O 仍不影响非零性 | 明确错误 | 同阶余项可能精确抵消首项。§8 给出反例于该推理，并补写稿件所需的非线性下界与受控极限。 |
| 四条以外都是已复算的局部代数 | 过度概括 | 报告自己承认未核全部区域的主化、共面积及一般阶系数估计。这些也是分析性的承重步骤。 |

因此，不建议照这份报告的建议盲目更换常数选择顺序、放弃物理归一化，或从头重构整篇论文。可以将下面的局部推导纳入下一版，但“证明完整”的判断仍须覆盖整个无限尾项。

## 2. 原样复跑与修正计算

原件哈希：

```text
checks.py
0348272c767a30804b4102511a34f427259f1c11df312f347b3142cc543230f9
ISING_AUDIT_REPORT.md
611bea00379d54db62cb5a5f460cbe629f3a6e699e3ee988573a052654e99375
```

复跑环境：Python 3.12.14、NumPy 2.3.5、SciPy 1.18.1。初次因缺少 SciPy 中止；安装到本任务工作目录后，原脚本未改动地完整执行。原始 stdout、stderr 均收入复核包。

### 2.1 可以复现的部分

Schur/Pfaffian 恒等式最大误差为 `1.6461335865920212e-15`；模平方恒等式最大误差为 `2.6645352591003757e-15`，与报告所列一致。这是浮点校准，不是全参数域证明。

### 2.2 “下半单位圆盘”采样实际上包含圆盘外点

脚本在矩形 `[-0.95,0.95]+i[-0.95,0]` 内采样，没有限制模长。按完全相同的随机调用顺序重放，3000 个点中有 **437 个在单位圆外**，500 组样本中有 **319 组包含越界点**，最大模长约 1.33694。

这不推翻半圆盘不等式；它说明这段实验并未按声称的定义域设计。修正脚本改用 `sqrt(U)*exp(-i*pi*V)`，确保样本在下半单位圆盘内。500 组六变量样本满足界，最大 Pfaffian 模约 0.03984。这仍只是抽样。解析证明来自模平方恒等式各项非负及 Schur 恒等式。

### 2.3 径向积分没有在原脚本中通过

原样执行的关键输出是：

```text
N=2: numerical = 1.234567901e-09 + 9.835238121e-18 i
     predicted = -0.4988691622 + 0.4988691622 i
     ratio ≈ -1.2e-9 - 1.2e-9 i
N=4: numerical = -2.323057313e-09 - 7.402694276e-17 i
     predicted = 0.3932682971 - 0.3932682971 i
     ratio ≈ -3.0e-9 - 3.0e-9 i
IntegrationWarning: The integral is probably divergent, or slowly convergent.
```

失败来自直接在 `[0,10^9]` 上自适应积分，未解析主要贡献的尺度。将 R=tan t 后，待检积分准确化为

\[
\int_0^{\pi/2}
\frac{\sin^{N^2-2}t}
{(Q\cos^2t-id\sin^2t)^{N^2/2}}\,dt.
\]

在 Q=1.7、d=0.9 下，用 mpmath 80 位精度计算，N=2、4、22 与 beta 闭式的相对差均小于 `1.2e-80`。这支持闭式而不是原脚本的方法。测试只涉及单位角权的径向部分，不验证完整角积分、无限尾项或第 241 阶导数的一致界。

### 2.4 留数脚本没有计算轮廓积分

原脚本只将 Res=i 代入 `2*pi*i*Res`，打印 **−2π**，并未积分。其“整条实线积分”说明也不合适：函数是周期函数，不能如此直接积分到整条实线。

修正检查使用

\[
f(v)=\frac1{1-e^{-A+iv}},\quad A=0.031,
\]

以及顶边 `[−π,π]`、底边 `Im v=−0.1` 的顺时针矩形。顶边从左向右的积分为 2π，底边从左向右为 0，竖边相消；故闭合积分为

\[
-2\pi i\operatorname{Res}_{v=-iA}f
=-2\pi i\cdot i=+2\pi.
\]

80 位数值计算与此一致。这核验了稿件的 +2π；原脚本的输出不能作为这一结论的复现证据。报告写出的新旧轮廓关系也须连同方向重写，不能仅凭最后一个正号判定全部符号一致。

## 3. 两个首阶图表之外：局部方法可以继续使用

定位：revision 2 的 **Lemma 4.3**，标签 `lem:complement`；独立 tex 第 483 行起。报告写作“Lemma 4.4”不准确。原始来源为 `COMPACT_PRIME_MEAN_RESIDUE_AMPLITUDE.md`，相应原始方法见 [Tracy–Widom 2014，§III 与 Appendix B](https://arxiv.org/pdf/1403.3966)。

不能在 Nickel 点直接调用该文的全局非 Nickel 定理。但是局部证明只需要当前图表的奇异因子梯度不具有非负零组合。下面把此条件及其结论写清楚；不把全局定理当作黑箱。

### 3.1 非负零组合只能在两个指定中心发生

记两个乘积因子的向量为 X、Y，成对因子的向量为 X_ij、Y_ij，色散向量为 Z_j=(α_j,β_j)，其中 α_j=Im x_j、β_j=Im y_j，其他分量为零。

若某 X_ij 在非负零组合中系数为正，其第 i、j 个正分量都要求相应 α_i、α_j 为负。但因子奇异要求 x_i x_j=1，故 α_i+α_j=0，矛盾。Y_ij 同理。因此组合中没有成对向量。

若 X、Y 都有正系数，逐坐标的平衡迫使每个 α_j、β_j 都严格为负，且 α_j/β_j 相同。令 u=cos θ、v=cos φ、u+v=S_*>0，则

\[
\frac{d}{du}\log\frac{\sqrt{1-u^2}}{\sqrt{1-v^2}}
=-\frac{S_*(1-uv)}{(1-u^2)(1-v^2)}<0.
\]

因此同一个比值只能给出一个下半圆的有序坐标对。所有 x_j 相等、所有 y_j 相等。两乘积奇异条件再要求这些共同坐标为 N_0 次单位根，稿件的唯一 cosine 对命题只留下两个交换后的中心。

若只有 X 出现，则每个 β_j=0。S_*>0 排除 y_j=−1，所以所有 y_j=1，所有 x_j 都等于下支 ξ=e^{-iθ_B}。这与 ξ 不是单位根相冲突。仅有 Y 的情况对称。两个乘积向量都没有出现时，各色散向量的支撑互不相交，无法相消；轴点退化已由所选点的条件排除。

故去掉两个中心的固定小邻域后，每个剩余中心的奇异梯度凸包确实避开零。这里得到的是局部非驻相条件，不只是“没有更强奇点方向”。

### 3.2 显式的参数计数

固定 N=N_0。某一局部图表有 m 个可能奇异的因子，给每个因子引入正参数 t_l，写 R=Σt_l。梯度凸包与零的距离为正，缩小角支撑后有

\[
|\nabla_\theta g|\ge cR,
\qquad |\partial_\theta^\nu g|\le C_\nu R,
\qquad \Re g\le0.
\]

这些是对径向趋近和取定的轮廓半径一致的局部估计。先做 j 次 s 导数：其角向振幅及固定阶角导数至多增加 `(1+R)^j`。当 R≥1 时，用

\[
\mathcal L=
\frac{\overline{\nabla g}}{|\nabla g|^2}\cdot\nabla,
\qquad \mathcal L e^g=e^g
\]

分部积分 M 次，每次获得一个 R^{-1}。共轭只用于复梯度的角向积分恒等式；参数导数在此前已经做完。取

\[
M=m+j+1
\]

即可得到正参数积分的径向主化

\[
R^{m-1}R^{j-M}=R^{-2},\qquad R\ge1.
\]

R≤1 的参数区域有有限体积且振幅有界。若 m=0，图表本来就是正则的。两个中心邻域以外是紧集，取有限覆盖；各图表的常数允许依赖固定 N_0、j 和所选点。

这给出全部固定 j 的有界性。所需的“额外分部积分次数”可以明确写出，没有出现必须另创新定理的障碍。这项局部核验不能替代高阶 N 尾项的统一估计，因为本节将 N 固定为 N_0。

## 4. pair 抑制：应核验一致紧性，不必求十进制 q

定位：Lemmas 7.2、7.3、8.3；tex 第 824、874、1283 行起。v38 对应 `PAIR_CONSTANTS_COMPLEX_DISK_FRESH_AUDIT.md`、`PAIR_COMPACTNESS_ENDPOINT_EQUALITY_AUDIT.md`、`LARGE_LAMBDA_COMPLEX_DISK_AUDIT.md`。

### 4.1 二次系数的符号是符号运算

令 a=−log q′>0，b=log(1+η)<a/4。同组对数不少于 N²/6−N/2，跨组对数不大于 N²/3，故

\[
\log\left|\prod_{i<j}P_{ij}\right|
\le-a(N^2/6-N/2)+bN^2/3
\le-\frac a{12}N^2+\frac a2N.
\]

可取 κ=a/12、C=e^{a/2}。命名的 Stokes 指标至多多出 N−1 个统一有界的 pair，仍只增加 C^N；对其余 N−1 个变量应用上述计数即可。三组计数本身由 Σn_g²≥N²/3 得到。修正脚本另枚举了 N≤200 的所有 1,373,697 个非负整数组合，仅作为有限算术检查。

所以报告要求 q 必须有一个具体数值，理由不成立。严格 q<1 的来源及其在参数域上的持续性，才是实质条件。

### 4.2 严格性的边界情形

在极限下半圆上，Schur 模平方恒等式给出跨组完整 pair 模不超过 1。三个组应满足：

1. B 是足够小的分支邻域。用正则坐标 φ，完整消去的 pair 为 `(φ_i−φ_j)^2 A_s(φ_i,φ_j)`，A_s 在固定邻域解析有界，故 B² 上严格小于 1。
2. L 与确切分支保持正距离，z 根处于严格子圆盘；对应 Schur 因子严格小于 1。
3. R 同样避开分支，z 根在与实轴分离的紧下半圆弧上；模平方恒等式中的 `4 Im z_i Im z_j` 给出严格性。

在 y=±1 的双端点使用完整消去式，分子趋于零；不要将两个可能分别呈现 0/0 的 Schur 因子拆开估计。

**如果让 L 或 R 包含确切分支，上述严格性会失败**：`|P(y_B,1)|=|P(y_B,−1)|=1`。这不是新发现，v38 和 v2 已明确记录，并用紧组与分支之间的固定间隙避开。它是今后改写时不能删掉的条件。

固定这三个组后，所有消去后的 pair 均在相应紧参数集上连续。双分支点处可从 `y_s(φ)` 的偶解析性直接看到 `(φ_i+φ_j)` 因子被消去。因此可以先取得 q<1，随后选 q′、η，最后缩短上端点小区间并减小形变量 τ。占据率 h=P/N 和 λ 可以放入整个 `[0,1]^2`；这扩大了待估计参数集，不需要把积分中的 P 当作常量。

可以把同组允许增量 q′−q 和跨组允许增量 η 各分成两份：中心处的端点延伸与形变只用掉一半，留另一半给复圆盘扰动。统一连续性给出相应的统一邻域。命名的上方紧变量所形成的 pair 单独估为常数：其根与下根的逆保持分离，只有 O(N) 个这样的 pair。

### 4.3 两种相关复圆盘

在 `|s−s_ε|≤cε` 上，分支根的正则 φ 位移至多为 `C sqrt(ε)`，紧根位移为 `Cε`；取统一的 ε_0 后，这些位移都落在上面的连续性余量内。根的色散虚部保持正量级，分支选择不会穿越切口。

在大电流圆盘 `δ_s=cλ_*/N²` 上，分支根的虚部余量至少为 `c_1(ε+λP/N)`。因 P≥1、λ≥λ_*，沿整个圆盘有

\[
|\Delta\phi|
\le C\frac{\delta_s}{\sqrt{\varepsilon+\lambda P/N}}
\le \frac{Cc\sqrt{\lambda_*}}{N^{3/2}}.
\]

紧根位移至多 Cδ_s。先选 c 足够小，便能在全部 N、λ、占据率上保留同一套严格余量；这里没有用一个固定 ε 的逐点连续性来替代一致性。

命名上方根在中心满足 `|z_q|≤e^{-c_q λ}`，圆盘中其他紧根的总膨胀至多 `e^{CNδ_s}`，而 `Nδ_s≤cλ/N`。再减小 c 即有 `|Z|≤e^{-c'_q λ}`。Y 的精确径向和给出另一个量级为 λ 的乘积间隙。

这些是对报告指定的一致性接口的补充核验。**Prop. 6.1 的 c/N 圆盘走的是另一条估计**：它利用紧变量数 M 的 `e^{-aM²}` 和阶乘衰减，不要求所有 N 个 pair 都先满足 Lemma 7.2 的二次抑制。报告把三个圆盘统称为同一个根的后果不准确。

## 5. e^{CN³} 与先 A 后 B：一个可直接检查的上界

定位：Prop. 7.6，tex 第 1016 行起；v38 的 `TWO_NONZERO_G3_FRESH_COAREA_PROOF.md`。此处只核验所质疑的三次系数来源及吸收，不把整个共面积证明视为已通过。

记 b_N=c_*e^{-(A+4)N}/N，ρ_N=e^{-BN}。在近碰撞补集，取 B 足够大使 `2ρ_N≤b_N/8`，由命名锚点得到所有坐标离分支至少为 b_N 的固定倍数。因此

\[
|\phi'(u)|\le C_1b_N^{-1/2},\qquad
|\phi_i-\phi_l|\le2C_1 b_N^{-1/2}\rho.
\]

设 D=N(N−1)，则

\[
|\Delta(\phi)|^2
\le (4C_1^2/b_N)^{D/2}\rho^D.
\]

再计入 N 个一体测度的斜率和有界解析 pair 系数，可以放大一个固定 K≥1，使未微分密度的正规系数至多为

\[
(K/b_N)^{N^2/2}.
\]

其对数为

\[
\frac{N^2}{2}\big[(A+4)N+\log N+\log(K/c_*)\big]
\le C_0N^3,
\quad
C_0=\frac{A+5+\log(K/c_*)}{2},
\]

这里取 c_*≤1，并使用 log N≤N、N²≤N³。C_0 是有限的，而且不依赖 B。

固定 j 的正规系数导数、微核 cutoff 导数至多再带来 b_N^{-c_j} 和固定次幂 N，属于 `exp(O_j(N log(N+1)))`。对近碰撞 cutoff `η(ρ²/ρ_N²)`，其导数支撑在 ρ 与 ρ_N 可比的环带，可将逆尺度全部计入明确保留的 ρ 负幂；其光滑函数的固定导数常数不依赖 B。剩余碰撞次数和有理权重的证明仍按 Appendix D 核验，不能从这个三次系数上界单独推出。

给定稿件中的剩余幂 `L=N²−2j−4`，主要指数准确展开为

\[
C_0N^3+L\log2-BNL
=-(B-C_0)N^3+(2j+4)BN+(N^2-2j-4)\log2.
\]

因此先固定 A、k、c_*、K，再取 `B>max(A+5,C_0+1)`，并按需增加 B 以保证尺度分离，足以压住所有足够大的 N。有限个余下 N 的最大值可并入依赖于固定点和 k 的常数。有限集合 `j≤k` 同时取最大值即可。

允许 C_0 依赖 A、k 不会形成循环。只有它依赖于尚待选择的 B，才会破坏这个选择。报告提出的“先 B 再 A”没有必要，并可能破坏已有的依赖顺序。

## 6. 覆盖性、一般阶归纳与尚未完成的工作

定位：Lemma 7.1、Lemma D.2、Appendix G；tex 第 786、1735 行起。v38 对应 `NESTED_ANGULAR_PARTITION.md`、`LIE_POLE_FILTRATION_PROOF.md`、`SECOND_FAMILY_TAIL_GLOBAL_JET_AUDIT.md`。

### 6.1 分划不因有限次求导增加新的支撑

对任意光滑权重 w 和多重指标 μ，

\[
\operatorname{supp}\partial^\mu w\subseteq\operatorname{supp}w.
\]

证明是：w 在其支撑以外的开邻域恒为零，全部导数同样为零。将这个事实用于稿件的精确 telescoping 恒等式

\[
1=\prod_i\chi_{B,i}
 +\sum_q(1-\chi_{B,q})\prod_{i<q}\chi_{B,i},
\]

每个补集权重及其全部有限 jets 都保留同一个外锚点 `|u_q|≥δ_B/2`。对其余坐标再展开

\[
1=\beta+(1-\beta)\ell+(1-\beta)r,
\quad \ell+r=1.
\]

左右 step 的过渡区完全落在 β=1 的开平台内，所以非分支权重及全部 jets 都避开内分支区。选择固定的大 L 后，真分支的斜率可统一压过外锚点斜率。这来自 `|b_j|≥cL/sqrt(δ_B)` 与外锚点的固定上界；在 λ≤λ_* 的中间窗口，有限 jets 的扰动趋于零。它不要求按 N 重选 L。

### 6.2 一般阶归纳已经有可用的形式

令每个带权图表使用自己的局部场 V_h，记 `D_h=∂_s−L_{V_h}`。在已核验穿孔通量消失的前提下，每次运算只能：对权重加一个角导数、对振幅或已有系数求导、或乘上场及其散度。归纳得到

\[
D_h^j(w_h A_s)
=\sum (\partial^\mu w_h)\,B_{j,\mu,h}(s,\theta),
\qquad |\mu|\le j.
\]

所以每一项仍落在原有图表的闭支撑上；场在图表间不必相等。对稿件的正规坐标场，把选定差值极点 δ=φ_p−φ_q 明确提出后，系数属于有界解析 germ 的乘积、至多 N 项的和，以及 δ^{-m}。一次固定阶运算只增加有限个因子及至多 N 个指标选择。因此归纳可给出 `C_j N^{a_j}` 型系数与项数界，a_j 是有限整数，不依赖 N、ε。无需运行第 1 到第 241 阶来代替这个证明。

这也解释了支撑结论为何能用于全部固定 j。命名 Stokes 指标的 p=1、m=0 平台及真分支的 p=0、m=1 平台均在开邻域内成立；所有权重 jets 仍在这些平台上。混合场只移动这些坐标，故 V(P)=V(Σm_i)=0 是函数恒等式，可继续微分。一般占据率的导数留在当前图表的系数中，不会生出一个未分类的角区域。

### 6.3 十三行的覆盖树

| 分流步骤 | 对应行 |
|---|---|
| 原始阶数超过 C_H(H+1)² | W1 |
| 其余阶数的最终选中轮廓 F | W2 |
| 当前积分 λ≥λ_* | W13 |
| 原始 K 或小电流，且 N≥D sqrt(H) | W3 |
| 中间阶 K，所有变量在 B：微核、远补集、近碰撞 | W4、W5、W6 |
| 中间阶 K，不全在 B：有紧左根、真分支与紧锚点混合、全紧右 | W7、W8、W9 |
| 中间阶小电流：有紧左根、真分支混合、全紧右 | W10、W11、W12 |

小电流不需要“所有变量都在 B”这一额外行，因为它总有一个上方紧的命名指标。N 和 λ 的阈值在求导后才划分，不产生阈值导数项。每项支撑保持，因此以上路由适用于所有固定阶密度。

**覆盖树闭合并不证明各行的估计正确。** 原审计明确没有重算全部共面积 Jacobian、相位映射重数、一体主化和穿孔通量。当前补充也没有把全部这些分析重新独立证明一遍。故不能把这些局部补充和有限计算相加，宣布 Theorem 9.1 或 Corollary 9.3 已经验证。

## 7. 归一化：可以直接回到物理关联函数

定位：Appendix F；原始来源 `FORM_FACTOR_NORMALIZATION_AUDIT.md`、`ONSITE_GROUPING_EXACT_AUDIT.md`。原始材料中的 Boukraa PDF 正文可用；报告所述“只拿到摘要”是该次审计的访问边界，不是资料本身缺失。

### 7.1 N 个角测度与 N 个辅助留数

[TW2014 Appendix A](https://arxiv.org/pdf/1403.3966) 的 Fredholm 展开使用 N 个 `dθ/(2π)`。令 x=e^{iθ} 后，每个变为 `dx/(2πix)`。再用

\[
\frac1{2\pi i}\oint
\frac{y^{n-1}}{D(x,y;s)}\,dy
=\frac{e^{-n\gamma(x)}}{\sinh\gamma(x)}
\]

替换一个关联函数因子；这是 y=e^{-γ} 的直接留数。每引入一个辅助 y 积分便多出一个归一化 `1/(2πi)`。因此有 N 对普通轮廓测度时，总因子为 **`(2πi)^{-2N}/N!`**。

非原点格点和将 X^mY^n 替换为

\[
\frac4{(1-X)(1-Y)}-\frac2{1-X}-\frac2{1-Y}
=\frac{2(X+Y)}{(1-X)(1-Y)}.
\]

原有测度中的 1/(XY) 随之给出稿件的 `2(X^{-1}+Y^{-1})`。这确认该归一化来自物理关联函数，而不是自由定义一个新 T_N。印刷主式的因子仍应作为测度差异记录，不能把这里的核验说成作者已经公布勘误。

### 7.2 独立全格点表示的变量对应

[Boukraa et al. 2008，(4)–(9)](https://arxiv.org/pdf/0808.0763) 的变量满足

\[
\frac1{2w}=s+s^{-1}=S,\quad
x_i=e^{-\gamma_i},\quad y_i=\frac1{\sinh\gamma_i}.
\]

其 `2 sqrt(x_i x_j)/(1−x_i x_j)` 等于 `1/sinh((γ_i+γ_j)/2)`。另一方面，利用

\[
\cosh\gamma_i-\cosh\gamma_j
=\cos\theta_j-\cos\theta_i
=2\sin\frac{\theta_i+\theta_j}{2}
   \sin\frac{\theta_i-\theta_j}{2},
\]

得到

\[
\frac{\sinh((\gamma_i-\gamma_j)/2)}
     {\sin((\theta_i+\theta_j)/2)}
=\frac{\sin((\theta_i-\theta_j)/2)}
     {\sinh((\gamma_i+\gamma_j)/2)}.
\]

故报告质疑的两个 pair 形式是同一个恒等式；TW Appendix A 本身也显示了它。

还可直接对 Fredholm 关联项求全格点和：横向 Fourier 和约束 `Σθ_i=0 mod 2π`，去掉一个归一化角测度；纵向和是 `Σ_{n∈Z}Z^{|n|}=(1+Z)/(1−Z)`。在实 s>1 可先用收敛调节的 Fourier 和再取极限，得到 Boukraa 的 (N−1) 维全格点公式。按粒子数逐阶便有

\[
C_N^{\rm std}=f_{00}^{(N)}+2T_N,
\qquad
\mathcal X=1-\mathcal M^2+2\mathcal M^2\sum T_N.
\]

这也解释四个标准有符号图表与两个 offsite 下支图表的关系。稿件 Appendix F 已有对应说明，可以用这段推导加固。

### 7.3 为什么“只改常数不影响无穷和”不是充分论证

两种印刷前因子的比是 `(2πi)^N`，随 N 改变，不能提到整个级数外面。单个固定 N 的非零性保持，并不自动排除重新加权后的无限抵消。若逐区尾项估计成立，它们可以吸收这类 `e^{O(N)}` 权重；那需要使用完整的尾项界。这里优先用物理公式解决归一化本身，而不靠非零性回避。

## 8. 首项余项必须是小 o；稿件的受控极限可具体展开

报告称即使余项只有 O(ε^{-1/2}) 也不影响非零性。这是错误的推理，因为

\[
L\varepsilon^{-1/2}
 +(-L\varepsilon^{-1/2})=0
\]

且第二项正是同阶大 O。这是对报告该推断的反例，**不是对 Ising 自然边界命题的反例**。

### 8.1 固定形状球上的下界

在真实均值留数之后，所有 y_j 在单位圆的固定正则弧上，写

\[
Z=e^{-A_\varepsilon(t)-iG_\varepsilon(t)},
\quad \rho^2=\sum_jt_j^2,\quad \sum_jt_j=0,
\]

其中常数相位 Nβ 为 2π 的整数倍。对固定 N_0，在足够小的固定球上有

\[
a\varepsilon\le A_\varepsilon(t)\le A\varepsilon,
\qquad -C\le g_\varepsilon''\le-c<0,
\qquad g_\varepsilon(0)-\beta=O(\varepsilon^2).
\]

最后一点来自 `S(s_ε)=S_*+2i sin(θ_*) ε+O(ε²)`，一阶扰动是纯虚数。Taylor 积分余项和零均值条件给出

\[
G_\varepsilon(t)
=N(g_\varepsilon(0)-\beta)
 +\sum_jt_j^2\int_0^1(1-v)g_\varepsilon''(vt_j)\,dv.
\]

当 ρ²≥Kε²、K 足够大时，|G_ε|≥cρ²/4；缩小固定球可使 |G_ε|<π。用精确恒等式

\[
|1-e^{-A-iG}|^2
=(1-e^{-A})^2+4e^{-A}\sin^2(G/2)
\]

得到 `|1−Z|≥c'(ε+ρ²)`。当 ρ²<Kε² 时，仅 `1−e^{-A}≥cε` 就足够，因为 `ε+ρ²≤ε(1+Kε)`。

报告说在 ρ²≲ε² 时三次项与 ε 同阶，也不正确：此时 `Σ|t_j|³≤ρ³=O(ε³)`。实际需要处理的是均值相位的 O(ε²) 偏移；上述两区论证已经处理。

### 8.2 为什么能得到小 o

留数后的 numerator 保留完整的 Δ(t)² 因子，固定阶 s 导数不消去这些碰撞零。最高 pole 阶 k+1 在 t=sqrt(ε)τ 后，由上界主化为

\[
\frac{C\Delta(\tau)^2}{(1+|\tau|^2)^{k+1}}.
\]

其径向密度为 `R^{N²−2}/(1+R²)^{k+1}`，尾部是 R^{-2}。故在扩大后的形状域上使用支配收敛，确实给出 ε^{-1/2} 的系数极限。较低 pole 阶 l+1≤k 的径向积分在 ε→0 时有界：最坏的 l=k−1 给出幂 `N²−2−2k=0`。乘上 sqrt(ε) 后趋于零。

因此可以把真实形状积分的这一局部受控极限补写严密；不能将大 O 与小 o 的区别降级为“只影响显示幅度”。

## 9. 引文、定位与证据边界

TW2014 的直接定理是偶数阶在非 Nickel 点处的 C∞ 边界延拓。其正文谈及更强的解析延拓时，还讨论了正则奇点 ODE 的条件，不能把更强结论无条件并入该定理。revision 2 使用的是光滑性；外部报告写“更强：可解析延拓”需要保留条件。[原文第 3 页及 §III](https://arxiv.org/pdf/1403.3966)

Boukraa 2008 的研究支持自然边界猜想，但单篇 2008 年摘要不能确认截至 2026 年的完整文献状态或新颖性。此次没有进行足够全面的优先权清查，保持 **NOVELTY NOT CLEARED**。无需为评价这份报告先断言成果已经是新定理。

几处影响查找的编号应修正：

| 报告写法 | revision 2 的实际位置 |
|---|---|
| Lemma 4.1 留数约化 | Lemma 2.1 |
| Lemma 4.2 均值留数 | Lemma 4.1 |
| Lemma 4.3 形状周期 | Lemma 4.2 |
| Lemma 4.4 补集 | Lemma 4.3 |
| Theorem 4.5 首个奇异项 | Theorem 4.4 |
| Prop. 8.5 大 λ | Prop. 8.4；8.5 是高阶 K/S |
| Lemma D.4 | 该编号不存在；相关通量论证在 Appendix D 的正文 |

这些编号错误本身不推翻一个数学异议，但会降低清单的可追踪性。

## 10. 当前可用结论与后续稿件的状态

1. 原报告没有找到反例；本次也没有发现原始 Ising 命题的反例。
2. 此次给出的局部补充支持“两图表补集的固定阶有界性”“pair 严格余量的参数计数及保护圆盘”“先 A 后 B 的吸收顺序”“固定分划的全阶支撑保持”等接口。它们不是从有限数值样本外推得来。
3. 四项指定接口均有原包来源和 v2 落点，不能据此指控重构遗漏核心证明链。
4. 整篇候选稿的无限尾项仍未完成充分独立核验，尤其不能用几条局部补充、正确的覆盖表和抽样共同替代各区域的积分估计。原报告也明确没有完成这些工作。
5. 下一版可以吸收这些推导，但须继续标为候选证明；下一轮审查应独立检查全部尾项估计及它们的拼接，而不是仅对报告四条质疑逐一“打勾”。这是下一轮的完整研究审查范围，不是声称本次已经穷尽的工作。

论文 PDF、tex 和用户原始文件均未修改。复核包另含原始附件、两篇原始文献 PDF、相关 v38 笔记、修正脚本及结果、完整性清单。

下面的规范化审计块仅描述**对外部报告中上述具体断言的复核**，不把“INTERNALLY EXHAUSTED”赋予整个 Ising 候选证明。整篇自然边界命题的验证状态仍为 UNRESOLVED。

```text
AI THEORETICAL-PHYSICS ADVERSARIAL AUDIT A1v2

ORIGINATING RUN STATUS:
NOT APPLICABLE

AUDITED CLAIM SET:
R1 supplied computation and its stated domains/results;
R2 local nonstationary-phase applicability at the selected Nickel point;
R3 need for a numerical q and the specified disk-continuity interface;
R4 alleged obstruction from C depending on A and the A/B selection order;
R5 finite-jet support coverage and need for explicit derivative enumeration;
R6 normalization comparison with the primary formulas;
R7 claim that a same-order O remainder cannot affect noncancellation;
R8 whether the four named interfaces have original-source and manuscript
counterparts, addressing the user's concern about reconstruction omissions.

CENTRAL CLAIM VERDICT:
NOT APPLICABLE

AUDIT COMPLETENESS:
INTERNALLY EXHAUSTED

STRONGEST SURVIVING RESULT:
The concrete report objections are resolved or narrowed as documented;
R7 is false, R1 is only partially reproduced, and no missing source chain
was identified among the four named interfaces. The full natural-boundary
theorem has not received a completed independent audit.

STRONGEST SURVIVING RESULT CLASS:
LOCAL TECHNICAL

FAILED-RUN MAJOR BYPRODUCT SURVIVED:
NOT APPLICABLE

LOAD-BEARING CUT SET:
For the report: reproducibility, local IBP counts, strict-pair quantifiers,
cubic-coefficient dependencies, support preservation, physical normalization,
and the small-o noncancellation condition.

FIRST FATAL OR LOAD-BEARING RISK:
The report incorrectly treats a same-order O remainder as harmless.
This is a flaw in the report's inference, not a counterexample to Ising.

FATAL FLAWS FOUND:
R7's implication is false. No fatal flaw in the Ising theorem established here.

UNRESOLVED LOAD-BEARING RISKS:
None within the concrete counterclaims and source comparisons resolved here.
Full sector estimates and the global proof remain outside this completed
report-level reassessment; they are not awarded a pass.

HIGHEST-PRIORITY AUDIT RESIDUAL:
NONE within the resolved report-level scope.

AUDIT RESIDUAL STATUS:
CLOSED-FAIL

HARD STOP CLASS:
NONE

BRIDGE ATTEMPTS ON BLOCKED RESIDUAL:
NOT APPLICABLE

UNTRIED ACTIONABLE AUDIT STEP:
NONE

SOURCE-SCOPE STATUS:
SCOPE MATCHED

PHYSICAL ADMISSIBILITY:
PARTIAL

EVIDENCE PROVENANCE FOR DECISIVE NODES:
Unmodified user report and script; unmodified v2 source and v38 notes;
TW2014 and Boukraa2008 full primary texts; direct mathematical derivations;
original execution logs; corrected numerical checks with recorded versions.

INDEPENDENT RE-DERIVATIONS:
Finite-rectangle residue integration; compact-domain radial quadrature;
parameter-power IBP count; symbolic contraction exponent;
branch-slope cubic coefficient; full-site angular normalization;
fixed-support induction; nonlinear shape lower bound.

COMPUTATIONAL REPRODUCTION:
HIGH-PRECISION CROSS-CHECK

ASYMPTOTIC / PERTURBATIVE CONTROL:
CONTROLLED ASYMPTOTIC

FIXED-THEORY VS FAMILY-OF-THEORIES STATUS:
NOT RELEVANT

SAME-ORDER COMPLETENESS STATUS:
PARTIAL

NOVELTY STATUS:
NOVELTY NOT CLEARED

SIGNIFICANCE STATUS:
NOT ASSESSED

REPAIR NEEDED FOR ORIGINAL CLAIM:
For the audit report: correct numerical provenance, remainder classification,
constant-dependency objections, source scope and labels. For the Ising paper:
incorporating local supplements does not replace full independent verification.

EXTERNAL VALIDATION:
NOT PERFORMED

NEXT STEP AFTER INTERNAL AUDIT CLOSURE:
Use the original candidate paper and this reproducible response as separate
inputs to an independent full-proof review; do not label the theorem proved.
```
