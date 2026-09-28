# 候选方法蓝图：需要重新证明的路线

**本文件主动传递方法，不传递有效性。** 定义可直接采用；凡涉及合法性、等式、界、覆盖、非零或一致性的句子都是证明义务。必须写出新的推导；复述蓝图、宣称“由紧致性显然”、套用一次数值检查都不算完成。允许修补或替换，但保留 TAIL 的对象和量词。

## M1. 用实际权重作轮廓分解

采用 R0 中含 1/N! 的顶次形式 \(\Omega_{N,s}\)。取光滑周期函数 \(p,m,a\in[0,1]\)，固定小的端点宽度 \(\delta>0\)：

- m 支撑于下分支 \(-\theta_B\) 的小邻域，并在所有真分支截断及其有限阶导数的闭支撑的一个开邻域上等于 1。
- a 在 \([\delta,\pi-\delta]\) 外为 0，在 \([2\delta,\pi-2\delta]\) 为 1；上分支 \(+\theta_B\) 以及 m 支撑的反射须位于 a=1 的开平台内。
- p 支撑于 (0,π)，在 a 和 a′ 的闭支撑的开邻域上等于 1。p 与 m 支撑不交。

这些宽度先于 \(\varepsilon,N\) 选择。固定 \(\tau>0\)，定义
\[
P=\sum_i p(\theta_i),\quad
h_i=-2\tau p(\theta_i)+\frac{\tau P}{2N}m(\theta_i),\quad
y_i(\lambda,\theta)=r\exp(i\theta_i+\lambda h_i),\quad0\le\lambda\le1,
\]
\[
\psi=\prod_i(1-a(\theta_i)),\qquad U_{\lambda,s}=\Phi_\lambda^*\Omega_{N,s}.
\]
拟重建的精确分解是
\[
T_N=F_N+K_N+S_N,\quad F_N=\int(1-\psi)U_{1,s},\quad K_N=\int\psi U_{0,s},
\]
\[
S_N=-2i\tau\int_0^1\sum_q\int(\partial_{\theta_q}\psi)U_{\lambda,s}\,d\lambda.
\tag{M1}
\]
验证完整闭合同伦，跟踪 z 的内根分支，证明所有真正分母不穿零，并导出带符号的 Stokes 项。不要把加权积分误认成同伦不变量。

可用于验算的归一化角 Jacobian 候选为
\[
M_{ij}=d_i\delta_{ij}+\frac{\lambda\tau}{2N}m_i p'_j,
\qquad d_i=i+\lambda(-2\tau p'_i+\tfrac{\tau P}{2N}m'_i).
\]
在命名 q 的电流支撑上应有 \(p_q=1,p'_q=m_q=m'_q=0\)。重建行列式、把角列换成同伦速度的 minor、归一化和方向。占据数 P 依赖全部角变量，不能当成逐变量积分中的固定参数。

## M2. 完整配对的严格余量与三个参数盘

尝试把扩大的下半圆支撑分成真分支 B、左紧致 L、右紧致 R，紧致部分排除精确分支。目标是在同组得到 \(|P_{il}|\le q'<1\)，跨组允许 \(1+\eta\)。命名电流 q 单独处理，只允许 \(C^{N-1}\) 成本。

候选计数：同组配对数至少 \(N^2/6-N/2\)，跨组至多 \(N^2/3\)。选择 \(\log(1+\eta)<-\log(q')/4\) 后，期望完整配对乘积得到 \(C^N e^{-\kappa N^2}\)。需要证明的是严格余量本身，而不只是这个整数计数。

请构造用于紧致性论证的实际参数集合和消奇坐标，覆盖双分支、双端点、互逆角、端点薄片、\(\lambda\in[0,1]\) 和实际耦合 \(P/N\in[0,1]\)。可以用解析紧致性给常数存在性，但必须展示延拓、连续性和严格不等式所在，不能仅命名一个“resolved compact set”。特别检查 \(|P(y_B,\pm1)|=1\) 是否成立及其影响：它会阻止不分组的全局逐对 q<1。

需要分别重建以下圆盘，不能互相替代：

| 对象 | 候选半径 | 待证明的保护机制 |
|---|---:|---|
| 原始轮廓、K、较高阶小电流 | \(c\varepsilon\) | 原始外部阻尼，实际所有支撑上的根和产品间隙。 |
| 完整最终选中积分 F | \(c/N\) | 一个 p=1 的固定向内指标产生固定产品间隙，真分支得到 1/N 保护。 |
| 大电流 \(\lambda\ge\lambda_*\) | \(c\lambda_*/N^2\) | 命名上方指标的 λ 级衰减吸收其余根的总膨胀。 |

在扩大后的盘中，紧致根可能有 \(|z|>1\)；目标应是控制整个 Z 及实际 pair 分母，不能假定每个根仍在单位盘内。对大电流，可从
\[
E=\varepsilon+\lambda P/N,\quad P\ge1,\quad
\delta_s/E\le c/(NP),\quad \delta_s=c\lambda_*/N^2
\]
寻找支撑一致的扰动界，并检验候选 \(|Z|\le\exp(-c_q\lambda+CN\delta_s)\)。

一体主函数应当能够逐变量合法积分。建议尝试
\[
|R(y;s)|\le C(|u|+\varepsilon)^{-1/2},\qquad u=\theta+\theta_B.
\tag{M2}
\]
右边不含耦合 P。真实分支中心的实位移需要保留 \(O(\varepsilon^2+t^2+|s-s_\varepsilon|)\)，其中 \(t=\lambda P/N\)。只在径向中心成立的展开不可直接推广到完整复圆盘。

## M3. 固定实积分域上的微分与通量

对实际实角权重 w，尝试用 \(\mathscr D=\partial_s-\mathcal L_V\)，在证明各阶段边界通量为零后建立
\[
\partial_s^j\int wA_s=\int\mathscr D^j(wA_s).
\tag{M3a}
\]
若 \((\partial_s-V\cdot\nabla)Y=(\partial_s-V\cdot\nabla)Z=0\)，两大全局核应保持简单。V 可以是复系数的实变量分部积分场，不必有真实流；实 cutoff 不需要也不允许被无依据地全纯延拓。

在原 all-B 区，尝试正则坐标 \(\phi=\arccos W\)，记坐标映射 \(\chi_s:u\mapsto\phi\)，以同一内根使 \(z=e^{-i\phi}\)。应核查
\[
R\frac{dy}{2\pi i}=-\frac{z}{\pi(1-y^{-2})}\,d\phi,\quad
P_{il}=(\phi_i-\phi_l)^2A_s(\phi_i,\phi_l),\quad
\mathscr N_s=\Delta(\phi)^2\mathscr A_s.
\tag{M3b}
\]
所有解析性和有限阶导数界须在指定邻域证明，不能消去一个表面分母后丢掉剩余奇点。

设 \(a_i=S'/W_{u_i}\)，\(b_i=\partial_{u_i}\phi_i\)，\(A=\sum_i a_i\)。对选中 pair q,r，候选双相位场为
\[
V_i=a_i\ (i\ne q,r),\qquad
V_q=a_q+\frac{Ab_r}{b_q-b_r},\qquad
V_r=a_r-\frac{Ab_q}{b_q-b_r}.
\tag{M3c}
\]
重建冻结等式及残余场。候选关键结构是 \(b_qb_r/(b_q-b_r)\) 只有一个 \(\phi_q-\phi_r\) 的差分极点。

希望完整 j 次操作写成
\[
(\partial_u^\mu w)\,\chi_s^*\left[
\frac{c_{j,\mu,\ell,\nu}\partial_s^\ell\partial_\phi^\nu\mathscr N_s}
{(1-Y_s)(1-Z)}\,d\phi\right],
\]
\[
m+|\mu|+|\nu|\le2j,\qquad \ell+|\mu|+|\nu|\le j,
\tag{M3d}
\]
其中 m 为显式选中差分极点阶数。必须完整归纳，包括已有系数、V、散度、实 cutoff 和分子的所有导数；并证明除显式极点外系数及项数为 \(C_jN^{C_j}\)。分子应保持未除以原 Vandermonde 的形式；额外未选中碰撞极点不能隐去。

可试用 \(M>2k+2\) 的有理权重
\[
w_{qr}=\frac{(u_q-u_r)^{2M}}{\sum_{i<l}(u_i-u_l)^{2M}}
\]
在离开全相等集处分配选中 pair。对选中对角管、全体相等球及部分碰撞交会，逐阶段证明通量消失。候选充分幂次分别为 \(h^{2M+1-2j}\) 和 \(\rho^{N^2-2j-3}\)。先固定 \(\varepsilon,N\) 去穿孔，再做边界一致估计；不要交换这两个步骤。

微分会击中若干 pair。若用“完整 pair 仍有二次收缩”，须证明对固定 j 的所有 N 的计数及常数调整，包括 N 接近 N0+2 的有限低阶区间；不能把 j 当成远小于 N² 的移动参数。

## M4. 最终 F、较高阶和超高阶

对 F，telescoping 选择一个 \(a_q>0\) 的指标即可保证 \(p_q=1\)，保护不能依赖 \(a_q\) 的数值下界。在 c/N 盘上先对完整积分作绝对界，最后使用 Cauchy。仅用于绝对估计的根分组可以随 s 改变，但不得对这些随 s 改变的分组积分分别求导。

设 M 为非真分支指标数（此处与权重指数 M 不同，正文请改名）。候选 Pfaffian 预算包含
\[
\exp(CN+CM\sqrt N-aM^2),\qquad
\int|\operatorname{Pf}A(y)|\lesssim C^N N^{N/4}(CN^3(H+1))^M.
\]
与一体/Jacobian 成本 \(C^NN^{N/2}\) 和 1/N! 结合，尝试获得
\[
C^N N^{-N/4}(CN^3(H+1))^M e^{-a_1M^2}.
\tag{M4}
\]
需重新证明这些估计和异常子集展开；完整匹配数、余 Pfaffian 子式以及 CM√N 损失必须入账。不能只把目标阶乘预算复述为定理。

超高阶原始积分可尝试无共轭 Schur 恒等式、Pfaffian 匹配和 L² 一体主函数。检查所需的是同一半圆盘条件而不只是 \(|z|\le1\)。期望的界见 `TAIL_COVERAGE.md`。较高阶 K 和小电流可尝试 cε 盘上的 Cauchy 加配对压缩，无须冒险扩大原始轮廓参数盘。

## M5. 中间阶 all-B

令 \(H=\log(1/\varepsilon)\)，只在 \(N<D\sqrt H\) 使用 \(\varepsilon e^{CN}\to0\) 等窗口比较。候选微核尺度
\[
b_N=c_*e^{-(A+4)N}/N,\quad
\psi_N=\prod_i\chi(u_i/b_N),
\]
其中 \(\chi=1\) 于 [-1/2,1/2]、支撑于 [-1,1]。利用 \(\xi^N\) 分离尝试保护 Y 核；一相位场逐个冻结 φ，结合分支曲线的锥、长度及 Laplace 表示处理简单 Z 核。候选微核界是
\[
e^{C_jN^2}b_N^{(N^2-1)/2}.
\tag{M5a}
\]
这是需要证明的实际积分界，不能只计算其指数。

在补集 telescoping 留下 \(|u_a|\ge b_N/2\) 的锚点及其全部 cutoff jets。取
\[
t=N^{-1}\sum u_i,\quad\rho^2=\sum(u_i-t)^2,\quad\rho_N=e^{-BN}.
\]
远区使用 M3 的双相位微分，**完成微分后**再按真实最小/最大坐标和符号划分绝对积分域，证明实际实 coarea Jacobian、像的长度及重数。正/负/跨符号配置都要覆盖；靠近分支尖端时不得全域假定实相位凹性。

近全相等区要求 \(2\rho_N\le b_N/8\) 对所有 N≥N0+2 成立，由锚点固定所有坐标的符号并离开真分支。候选预算保留 \(e^{C_0N^3}\) 的几何损失，不能改称多项式。正均值情况下尝试以平均角和形状半径换成两个实相位，证明 Jacobian 至少 cNρ，并检查剩余幂
\[
L=N^2-2j-4\ge4N_0+2>0,
\]
\[
e^{C_0N^3+C_jN\log(N+1)}(2e^{-BN})^L(H+N)^2.
\tag{M5b}
\]
必须证明 C0 在选 B 前已固定，且不依赖 B。负均值分支的处理也要给出。半径换成相位后，先在支撑上界定其剩余正幂，不能把该半径再积一遍。展开相位的周期数、像长 CN 和实映射重数是不同成本。

## M6. 混合与全紧致区

构造嵌套 branch cutoff：外层半径 \(\delta_B\)，内层 \(r_0=\delta_B/(2L^2)\)。外层补集提供固定外锚点，内层为真分支；选择 L 使混合区分支斜率与紧致锚点斜率分离。有效左/右紧致标签都须离精确分支固定距离。周期标签的额外接缝应放在 a=1 的开平台，并核查所有相关权重及有限 jets 在那里消失。

原 K 取 λ=0。小电流中，命名 q 在 p=1,m=0 平台，真分支在 p=0,m=1 平台；沿这些方向作场才有希望精确保持 \(\sum p_i\) 与 \(\sum m_i\)。不能把耦合变形误当成各坐标独立变形。

混合图表用真分支的 φ 坐标与紧致实角的混合顶次形式，保留完整 Jacobian。若真分支集合为 J，设
\[
a_i=(\partial_s\phi_i)/b_i,\quad b_i=\partial_{\theta_i}\phi_i,
\quad A=\sum_{i\in J}a_i,\quad D_s=\sum_{i\notin J}\partial_s\phi_i.
\]
选真分支 j 和紧致 q，可试
\[
X_v=\frac{D_s+b_qA}{b_j-b_q},\quad
V_i=a_i\ (i\in J\setminus\{j\}),\quad
V_j=a_j+X_v,\quad V_q=-A-X_v,
\]
其余分量为零。需要验证实际耦合导数、平台条件、两个乘积冻结以及所有高阶阶段的合法性，而不只是形式代数。

左紧致根可能给固定 Z 间隙；全紧致右区可尝试真实相位曲率、交换对称性的光滑差分除法以及有理权重。实 bump 不全纯，不得使用虚假的全纯除法。形状半径与最大差分只保证 \(\rho\le\sqrt N\,d\)，相应成本必须入账。各区完整微分密度及 coarea 应在本次重建，不能用 all-B 的结论作口头类比。

## M7. 常数选择与最终求和

建议顺序：固定点及 k → 分支/紧致邻域与有限 jets → 极限同组严格性 q → q′、η → 端点薄片、τ → 三盘常数与共同 κ → C_H、α0、D 和有理权重阶 → resultant A、c* → 锚点几何中的 C0 → B 及其他指数尺度 → 一个共同 ε0。

只是一张候选依赖图；你须证明每步可行，找出任何隐藏循环。几何包含需对所有 N 成立，不能靠放大数值常数修补错误支撑。有限低 N 的数值上界可以单独处理。

最后按 `TAIL_COVERAGE.md` 合成各窗口，先建立每个固定外部点的合法逐项微分，再按 ε 分窗求和。必须对全部 0≤j≤k 成立，才能接入 BULK 的 Leibniz 法则。
