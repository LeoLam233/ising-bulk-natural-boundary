# Ising v7 — A1v2 内部敌对审计

## 结论

中央候选证明：**SURVIVES INTERNAL HOSTILE AUDIT**。
本轮未发现可否定 v7 承重论证的具体错误。这里的通过是本轮内部审计结论，不是独立人类专家认证、形式化证明或完整文献优先权认证。

正确性审计的关键是完整无限尾和中高阶微分与碰撞控制，并非首项低阶数值验证。相关推导及独立首项复算见 `INDEPENDENT_DERIVATIONS.md`。

完整优先权清查未完成（H7）。已核对控制性原始文献，并检查对角 susceptibility / Toeplitz 扩展及不同解析变量的 2026 Ising 一点函数结果；不能据有限检索宣布全球首证。未使用旧审计 PASS/CLOSED 标签作为数学前提。

## 文件

- `INDEPENDENT_DERIVATIONS.md`：平均角留数之外的全站点首项推导、Gaussian/Schwinger 形状积分、全阶 Lie 递推、通量、coarea、参数圆盘及窗口求和。
- `CLAIMS_AND_RESIDUALS.md`：逐项结论、残余风险、限制与来源。
- `checks.py`：精确符号恒等式、有限状态递推检查、90 位物理色散诊断和首项系数诊断。
- `check_results.json` / `check_run.log`：本轮实际执行的输出。
- `independent_normalization.py`：独立标准角积分与 reduced contour 的二粒子归一化比较。
- `independent_normalization_results.json`：实际执行的双精度结果。
- `MANIFEST.sha256`：本输出包文件的 SHA-256；输入三文件哈希在 `check_results.json` 中。

原研究的 checkpoint、原始程序及历史审计附件没有随本次三个输入文件提供。本包是本轮新建的审计诊断，不是对未提供的原研究包进行复现。

## 复跑

本次环境：Python 3.13.5、SymPy 1.14.0、mpmath 1.3.0、NumPy 2.3.5。

```sh
python checks.py
python independent_normalization.py
```

`checks.py` 中输入哈希扫描使用本次会话的 `[LOCAL_PATH_REDACTED]`。在其他环境缺少这些输入时，会跳过不存在的输入，不影响主要数学诊断；要重新核对输入哈希，请将三个原附件放在对应目录，或修改该脚本最后的输入路径。

## 证据边界

解析归纳和一致界负责普适结论；有限样本和高精度小残差不能代替它们。没有区间算术包围、没有对完整 241 阶多粒子积分直接数值求导、没有 Lean 形式化、没有外部人类专家复现。25 点网格的 pair 最大值不是连续支持上的严格上确界。


---

# v7 审计：独立推导与危险接口复核

对象：`ising_audit_manuscript_v7.tex` / `.pdf`，2026-09-28。
本文件是审计推导，不是原作者补写证明；没有改变模型、猜想、点集、导数阶或粒子数窗口。

## 1. 从全站点角积分核对首项，不经过平均角留数

独立起点为 Boukraa et al., arXiv:0808.0763v1, equations (4)–(9)，其低温标准粒子项满足

\[
C_N^{\rm std}=\frac1{N!}\int_{\sum_i\phi_i=0\ ({\rm mod}\ 2\pi)}
\prod_{i<N}\frac{d\phi_i}{2\pi}\;
\prod_i\frac1{\sinh\gamma_i}\;
\frac{1+Z}{1-Z}
\prod_{i<j}\left[\frac{\sin((\phi_i-\phi_j)/2)}{\sinh((\gamma_i+\gamma_j)/2)}\right]^2,
\qquad \cosh\gamma_i=S-\cos\phi_i.
\]

源文的 `x_i` 是这里的 `z_i`；源文的 `y_i` 是 `1/sinh(gamma_i)`，并非双轮廓变量。

在第一选定阶 N=N0 的图表中令 phi_i=-alpha+t_i，sum t_i=0。采用外部芽所固定的根，gamma_i=i varphi_i；在中心 varphi_i=beta。直接 Taylor 展开而非移动平均角轮廓，得到

\[
1-Z=Q\varepsilon-id\sum_i t_i^2+\text{更高阶项},\qquad
Q=\frac{2N\sin\theta_*}{\sin\beta},\quad
 d=\frac{S_*(1-\cos\alpha\cos\beta)}{2\sin^3\beta}>0.
\]

每一对的最低项为 `-(t_i-t_j)^2/(4 sin^2 beta)`，每个一体因子为 `1/(i sin beta)`。N 偶数时两类符号乘积为正。因此全站点单图表最低密度常数为

\[
\frac{2}{N!}(2\pi)^{-(N-1)}2^{-N(N-1)}\sin(\beta)^{-N^2}
=2\pi K_\beta.
\]

这里的 2*pi 来自少一个角积分的归一化，不借用原手稿平均角留数的正号。分母 s 导数为 D_s=-i N S'(s*)/sin(beta)，故这一图表的第 k 阶导数系数正是

\[
2\pi K_\beta(-1)^k k!D_s^k J_\beta=L_\beta.
\]

角反射使正负图表相同；alpha/beta 交换后的正弦总幂为

\[
-N^2-k+\tfrac12+3\tfrac{N^2-1}{2}=0.
\]

全部剩余因子亦交换不变，所以四个全站点图表给出 4 L_beta。另一方面，直接逐站点求和给出 C_N^std=f_00^(N)+2T_N；无全局乘积核的 onsite 项在此点的局部梯度锥不存在坏组合，因而固定阶导数有界。故离站点项的系数是 2 L_beta。

这一路线独立核对了测度、符号和图表重数；它仍共同使用正确的物理根及同一个可独立核验的局部二阶展开，并不是全问题的独立外部重证。

## 2. 形状积分：Gaussian/Schwinger 路线

令 a0=(N^2-1)/2, n=k+1=N^2/2。考虑

\[
I_N(a)=\int_{\mathbb R^{N-1}}\Delta(t)^2e^{-a\sum_{i=1}^N t_i^2}\,dt_1\cdots dt_{N-1},\quad t_N=-\sum_{i<N}t_i.
\]

对 Re(a)>0，由齐次性 I_N(a)=a^{-a0}I_N(1)。也可不把角向正数 C_N 当作黑盒：单首项 Hermite 多项式对权 e^{-x^2} 的平方范数为 sqrt(pi) 2^{-r} r!。范数由 Rodrigues 公式和 r 次分部积分得到。将 Vandermonde 写成这些单首项多项式的行列式并展开，正交性给出

\[
\int_{\mathbb R^N}\Delta(x)^2e^{-\sum x_i^2}\,d^Nx
=\pi^{N/2}2^{-N(N-1)/2}\prod_{r=1}^N r!.
\]

令 v=sum x_i, x_i=t_i+v/N。该坐标的绝对 Jacobian 是 1，sum x_i^2=sum t_i^2+v^2/N；积分掉 v 得

\[
I_N(1)=\frac{\pi^{(N-1)/2}}{\sqrt N}\,2^{-N(N-1)/2}\prod_{r=1}^N r!>0.
\]

与形状极坐标比较还得到

\[
C_N=\frac{2^{1-N(N-1)/2}\pi^{(N-1)/2}}{\sqrt N\,\Gamma(a_0)}\prod_{r=1}^N r!.
\]

现在先在 Re(a)>0 使用 Schwinger 参数，而不是直接对复二次型套实积分表：

\[
\begin{aligned}
J(a)&=\int\frac{\Delta(t)^2\,dt}{(Q+a\sum t_i^2)^n}\\
&=\frac1{\Gamma(n)}\int_0^\infty u^{n-1}e^{-Qu}I_N(au)\,du\\
&=\frac{C_N}{2}\frac{\Gamma(a_0)\Gamma(1/2)}{\Gamma(n)}\,a^{-a_0}Q^{-1/2}.
\end{aligned}
\]

在右半平面内操作绝对收敛。沿 a=eta-id, eta>=0 取 eta 向零：由于 d,Q>0，分母绝对值统一控制 1+|t|^2；径向大半径衰减为 R^{-2}，可用支配收敛。因此到达手稿指定分支的 a=-id，得 J_beta=(C_N/2)Q^{-1/2}(-id)^{-a0}B(a0,1/2)，非零。

这一重推导验证复相位不能任意改成绝对值，也不容许将尚未积分的平均角/形状联合绝对值用作支配函数。

## 3. 运输场、高阶递推与边界通量

这是本轮最主要的尾和审计。

在原始全分支图表中，a_i=S'/W_{u_i}, b_i=partial_{u_i} varphi_i, A=sum a_i。对一对 p,q 定义

\[
V_i=a_i\ (i\ne p,q),\quad
V_p=a_p+\frac{A b_q}{b_p-b_q},\quad
V_q=a_q-\frac{A b_p}{b_p-b_q}.
\]

直接求和得 sum V_i=0，sum b_i V_i=sum a_i b_i=partial_s sum varphi_i。因此 Y,Z 同时被冻结。规则坐标中 B=partial_s chi_s-(chi_s)_*V 仅有

\[
B_p=-\frac{A b_pb_q}{b_p-b_q},\qquad B_q=-B_p.
\]

由局部反函数 y_s(varphi) 为偶解析函数，可写 b(varphi)=B_s(varphi)/varphi，B_s 偶解析且非零。于是

\[
\frac{b_pb_q}{b_p-b_q}=\frac{H_s(varphi_p,varphi_q)}{varphi_q-varphi_p},
\]

分子解析；没有额外的单体 1/varphi 分支极点。这一点比在未正则化角变量中粗估每次参数导数关键。

对原实角域上的光滑权 w，不作复解析延拓，恒等式是

\[
(\partial_s-\mathcal L_V)(w\chi_s^*\Omega_s)
=w\chi_s^*(\partial_s+\mathcal L_B)\Omega_s-(V\cdot\nabla_u w)\chi_s^*\Omega_s.
\]

它来自参数依赖 pullback 的导数和顶形式散度。积分分部允许 V 有复系数。若核 K=(1-Y)(1-Z)，则 (partial_s+B dot grad)K=0，核保持简单。

不除以 Vandermonde，保留整个分子 N_s=Delta(varphi)^2 A_s。j 阶项按选定差极点阶 m、原实截止函数阶 |mu|、规则坐标分子导数阶 |nu|、参数分子导数阶 ell 分类。每次操作只有：

* 对系数作固定 varphi 的 s 导数：m 不增；
* B dot grad 系数或 div(B)：m 至多增 2；
* B dot grad 分子：m 至多增 1，|nu| 增 1；
* 分子 s 导数：ell 增 1；
* 截止项：m 至多增 1，|mu| 增 1。

由归纳，m+|mu|+|nu|<=2j 且 ell+|mu|+|nu|<=j。对旧场、散度和系数的导数均已包含，不是只核验一阶再猜高阶。固定 j 下展开项数与被改动因子数的成本为多项式 N；剩余完整 pair 按组计数继续给出 e^{-kappa N^2+O_j(N)}，不是将总乘积除以可能为零的某个 pair。

对 M>2k+2 的实有理权

\[
w_{pq}=\frac{(u_p-u_q)^{2M}}{\sum_{i<l}(u_i-u_l)^{2M}},
\]

其截止导数和上述极点相配，只产生最大间距 d 的 d^{-2j} 成本。选定对角管通量充分上界为 h^{2M+1-2j}，全相等球通量充分上界为 rho^{N^2-2j-3}。尾部 N>=N0+2, j<=k 时两者指数均正。先固定 epsilon,N 去掉穿孔，再取边界极限，因此没有用 epsilon 非一致的通量估计交换两个极限。

## 4. 近全相等区：不能漏掉的三次指数

原始全分支近区的外锚点 |u_a|>=b_N/2 与 2rho_N<=b_N/8 推出 |u_i|>=b_N/4 且同号。b_N 按 N 指数变小，故转换分支导数及 Vandermonde 后确实可能出现 e^{C N^3}；不能把它写成多项式。

形状测度为 rho^{N-2}，分子零点总阶为 N(N-1)，j 次 Lie 操作和保守额外损失最多 2j+1。再用 (t,rho) 到两实相位的 Jacobian 下界 c N rho，保守剩余幂为

\[
L=N^2-2j-4\ge4N_0+2>0.
\]

rho 被 coarea 换成相位后不再是独立积分变量。先用 rho^L<=(2rho_N)^L，得到

\[
e^{C N^3+C_jN\log(N+1)}(2e^{-BN})^{N^2-2j-4}(H+N)^2.
\]

其对数为 (C-B)N^3+O(N^2)+B(2j+4)N+O_j(N log N)。C 在选 B 前由 b_N 锚点确定；选 B 足够大可压住所有充分大 N，余下有限 N 只改变点依赖常数。几何支持包含必须先对每个 N 成立，不能事后用常数补救。v7 的 Gamma_* 选择正好给出这个顺序。

## 5. 实 coarea 与混合扇区

全分支远区，两正端点 m,M 的相位图为 (m,M)->(m+M+const,x(m)+x(M)+const)。Jacobian 为 x'(m)-x'(M)。当 m<=M/2 且 M/epsilon->infty 时，两个分支测度除 Jacobian 不超过 C M^{-1/2}；可比端点时不超过 C sqrt(M)/(M-m)。M>=b_N/2 和 M-m>=rho_N/sqrt(N) 把成本变成 e^{O(N)}，而不是 epsilon 的负幂。这里只在完成微分后的绝对积分中选真正的最小/最大下标。

近区固定形状方向时，F=Nt 固定 t，严格凹性给 G 对 rho 单调，因此未展开相位图的重数为 1。相位区间长度可能为 C N，并非一个周期。两个简单周期核的积分因此付 C N^2(H+N)^2；此周期成本不能省略，也不能与已计重数再重复。

混合 Stokes 图表中，所选紧致上角 q 在 p=1,m=0 平台，真分支角在 p=0,m=1 平台。运输方向和所有支持内高阶导数均保持 P=sum p_i 及 sum m_i。冻结 Y 的验证因此适用于实际耦合轮廓，而不是错误地把全局占据量视作无关常数。完整三角 Jacobian 与原始电流权 -2 i tau partial_q psi 保留在顶形式内。

## 6. 参数圆盘与完整求和

三个圆盘不能交换使用：原轮廓 c epsilon；最终选定积分 c/N；大 lambda 电流 c lambda_*/N^2。后两个圆盘允许紧致根略离开单位圆；命名上角的固定或 lambda 级衰减吸收总计 N 倍根膨胀。分支仍在保护的内根支上。一体积分上界 C/(|u|+epsilon)^{1/2} 与耦合占据量 P 无关，故可逐角积分。

取 H=log(1/epsilon)，固定 j<=k。除超高阶外，四类总成本分别为

\[
\exp(O_j(\log^2 H)),\quad
\exp(\alpha_0(j+2)H),\quad
\exp((j+2-\kappa D^2)H+O_j(\sqrt H)),\quad
\exp(O_j(\sqrt H\log H)).
\]

alpha_0<1/[2(k+2)]，kappa D^2>k+2，故均为 o(exp(H/2))。超高阶 N>=C_H(H+1)^2 的 Pfaffian/阶乘估计比任意固定 epsilon 幂还小。所有 N 窗口和 lambda 分割均在完成微分后引入。由于 j 的集合有限，同一 epsilon_0 和常数选择顺序覆盖 j=0,...,k。

这样核对的是完整尾和，而不是固定 N 的局部估计。最后用所有低阶导数的尾界进入 Leibniz 规则，得到全体磁化率的非零首项，稠密点集排除任一点的局部全纯延拓。


---

# 逐命题审计与残余账本

## 审计对象及来源隔离

仅把本次 v7 PDF/TEX 作为被审论文，按随附 A1v2 工作。会话已有历史项目摘要，但未把过去的审计意见或成功标签作为证明前提；没有另行检索旧审计或旧 checkpoint。此次不是 clean-room 盲发现：审计员看过作者的方法与附录。

三个附件均在本轮计算中记录 SHA-256；没有用户提供的独立原始 manifest 可作反向验证。PDF 34 页。已查看关键公式的渲染页面，并与 TEX 对读。

## Claim inventory

| ID | 精确对象 | 本轮结论 |
|---|---|---|
| C0 | 零场、各向同性、无限正方晶格低温纯相的完整体磁化率外部芽，以 s=sinh(2 beta J) 为变量；单位圆是自然边界 | SURVIVES INTERNAL HOSTILE AUDIT |
| C1 | 所选素数点族稠密，第一偶数 Nickel 阶恰为 2p，首阶无序余弦对唯一，分支根非单位根并有指数分离 | 内部解析重推导通过 |
| C2 | 第一项 k=N0^2/2-1 阶导数为 2L_beta epsilon^(-1/2)+o(epsilon^(-1/2))，L_beta 非零；较低导数有界 | 平均角路线及独立标准角积分路线一致 |
| C3 | 对全部 0<=j<=k，sum_(N>N0,even) |T_N^(j)|=o(epsilon^(-1/2)) | 内部完整扇区/窗口审计通过；无数值穷举冒充无限和 |
| C4 | 加权 Stokes 恒等式、固定实截止函数的高阶 Lie 递推以及逐阶段无穿孔通量 | 内部重推导通过，另有符号和有限状态诊断 |
| C5 | 首项非零及全部低阶导数尾界推出完整体磁化率无抵消、进而自然边界 | 独立逻辑检查通过 |

本文自身没有提出独立验证或优先权已经完成的命题；不对作者未提出的优先权宣称作否定判定。

## 最小承重依赖集合

物理归一化/表示 -> 首项两个图表的精确局部拼接与非零同相系数；
完整实域加权回缩 -> 保护圆盘、完整 pair 严格分组收缩、分支正则化；
冻结双核的全阶 Lie 递推 -> 有理权吸收选定差极点及通量消失；
锚点/coarea/常数顺序 -> 全部导数的绝对尾界；
外部局部正规收敛 + 上述两条主估计 -> 体磁化率 Leibniz 规则 + 稠密性。

## Audit Residual Ledger

| ID | 决定性攻击 | 状态 | 依据及限制 |
|---|---|---|---|
| R1 | 双轮廓测度是否误差一个 (2pi i)^N；第一项正号和四/二图表是否相容 | CLOSED-PASS | 原始归一化公式；独立全站点局部推导；三温度三网格 N=2 数值比较仅作辅助 |
| R2 | 光滑角权是否非法穿越 x 留数或复平均角变形；Nickel 点余区是否误用非 Nickel 定理 | CLOSED-PASS | y-only 权先分区；硬平均段仅跨分离边缘；余区直接使用局部梯度锥有限覆盖 |
| R3 | 加权变形遗漏 Stokes 电流或电流符号/替换 minor 错误 | CLOSED-PASS | 秩一 Jacobian 与命名 q 的行列结构、Cartan 顶形式恒等式 |
| R4 | 高阶导数引入未计分支极点、对旧运输场漏导数 | CLOSED-PASS | 规则坐标 b=B(varphi)/varphi；五类归纳覆盖旧场与散度；有限检查不替代归纳 |
| R5 | 部分碰撞或全相等处遗失通量 | CLOSED-PASS | 有理权选定管指数 2M+1-2j；全相等指数 N^2-2j-3；先固定 epsilon,N 去穿孔 |
| R6 | 二重全局核 coarea 无法吸收分支测度，或周期/重数漏计 | CLOSED-PASS | min/max Jacobian 比率；近区固定形状射线重数 1；显式 CN^2 周期成本 |
| R7 | 指数小锚点导致 e^(CN^3) 无法被近碰撞控制吸收 | CLOSED-PASS | 常数 C 先于 B；L=N^2-2j-4>0；固定 B 后再统一 epsilon_0 |
| R8 | 耦合占据量 P 的角导数造成混合图表漏项 | CLOSED-PASS | 平台上运输场严格保持 P 和 sum m_i；包含全部三角 Jacobian |
| R9 | 原始 c epsilon、选定 c/N、电流 c lambda_*/N^2 圆盘偷换，根离开单位圆后沿用错误不等式 | CLOSED-PASS | 对紧致根允许小膨胀；命名锚点吸收 N 倍膨胀；分支保留保护 margin |
| R10 | 完整 pair 在端点只等于 1，严格收缩失效 | CLOSED-PASS | 不能用全对统一严格界；分组同组严格及跨组 slack；端点等号被实际数值诊断重现 |
| R11 | 从固定 N 有界跳到无限 N；低阶导数遗漏；移动窗口被求导 | CLOSED-PASS | 全部四类窗口成本逐项小于 e^(H/2)，超高阶单独 Pfaffian/阶乘界；先求导再分窗 |
| P1 | 有限网络检索是否足以排除全部先前等价证明 | OPEN-BLOCKED | H7 PRIORITY-CLEARANCE LIMIT；控制性源已核对，但检索覆盖不足以认证全球优先权 |

没有遗留被本轮明确识别、仍可立即执行而未执行的承重正确性测试。此陈述不宣称不存在未知数学错误或新的攻击方案。

## 原始文献对照

1. Tracy–Widom, *On the singularities in the susceptibility expansion for the two-dimensional Ising model*, arXiv:1403.3966v1, J. Stat. Phys. 156 (2014), 1125–1135。核对固定偶数阶非 Nickel 光滑性、局部梯度锥以及 Appendix A 归一化。该结果没有替本文证明无限尾和无抵消。
2. Boukraa et al., *Experimental mathematics on the magnetic susceptibility of the square lattice Ising model*, arXiv:0808.0763v1, J. Phys. A 41 (2008), 455202。核对 equations (4)–(9) 的低温全站点角积分、变量替换和平方 pair。
3. McCoy–Maillard, *The importance of the Ising model*, arXiv:1203.1456, Prog. Theor. Phys. 127 (2012), 791–817。振幅比较不是本轮归一化公理。v7 已将角符号、外部支及图表重数区别开；不把单纯复相位差当作主定理反例。
4. Tracy–Widom, *Natural Boundary for a Sum Involving Toeplitz Determinants*, arXiv:1502.04922。其起点是对角磁化率，并推广 Toeplitz/Fisher–Hartwig 符号，不是当前完整体磁化率的同一结论。
5. Assis et al., *Analyticity of the Ising susceptibility: An interpretation*, arXiv:1705.02541v2。检查摘要所述配分函数零点、等模曲线与 Nickel 奇点的关联；未据摘要宣称全文完成或否定某普适证明。
6. Yizhuang Liu, *Analyticity, asymptotics and natural boundary for a one-point function of the finite-volume critical Ising chain*, arXiv:2604.06011。摘要对象是把有限链长度 N 解析延拓的一点函数；变量、可观测量与本稿不同，不能作为同一问题已经解决的证据。

直接结论、方法关键词、隐藏等价/邻近对象三类检索均已尝试。部分检索结果相关性很低，不能计作强覆盖。新颖性标为 NOVELTY NOT CLEARED；没有外部人类/研究组认证。

## 对“通过”的严格限制

本轮不把内部自洽等同于外部真伪终审；不声称对完整无限维积分做了有限机器证书；不把 N=2 基准当作 N0=22,k=241 的证明；不把 90 位一致当作误差区间；不声称独立发现本证明。已保留下来的主张正是论文原范围，而非退化为对角磁化率或有限 form factor。

下一项真正外部工作是由未参与此推导链的专家从标准角积分重新建立统一尾界及进行完整文献优先权清查。此建议不是把本轮仍未闭合的已知可执行数学节点转交出去。
