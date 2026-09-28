# 审计结论

**本轮没有找到足以推翻 v7 的确定性数学错误，也没有找到一个能够明确判定为未闭合的关键证明接口。** 首项振幅的计算可以重建；尾和论证中的粒子数窗口、Stokes 修正、碰撞阶数损失和相位积分代价，目前没有出现相互矛盾的量级要求。

但这不是对自然边界定理的独立认证。**我对算术、归一化、首项留数和形式微分恒等式的把握，强于对整条高维尾和估计链的把握。** 剩余审计不确定性主要集中在命题 6.1 的复参数盘估计，以及命题 8.1–8.2 与附录 D 之间的高阶密度控制；下面会具体说明，而不是把“不确定”冒充已发现的漏洞。

正文和附录 A–G 的检查整理成了 **89 项审计矩阵**，另附独立计算程序、运行结果和覆盖范围说明：

[interface reference omitted]查看完整审计矩阵 [archival local link omitted]　｜　[interface reference omitted]下载审计与复算包 [archival local link omitted]

---

## 一、先确定真正需要击穿的地方

论文的结论依赖两件不同的事：

\[
T_{N_0}^{(k)}(s_\varepsilon)
=
2L_\beta\varepsilon^{-1/2}
+
o(\varepsilon^{-1/2}),
\qquad L_\beta\ne0,
\]

以及

\[
\sum_{\substack{N>N_0\\N\ {\rm even}}}
|T_N^{(j)}(s_\varepsilon)|
=
o(\varepsilon^{-1/2}),
\qquad 0\le j\le k.
\]

**证明首项奇异而不证明无限尾和不能抵消它，不够；只估计尾和的第 \(k\) 阶导数，同样不够。** 后者会遗漏乘上 \(\mathcal M^2(s)\) 后 Leibniz 公式中的低阶导数项。v7 在论证目标上没有犯这两个错误。[interface reference omitted]

外部文献也没有被不当地用来跨越这个缺口。Tracy–Widom 的相关结果针对固定偶数阶 form factor 的非 Nickel 点边界光滑性；其原文明确指出，无限和中的奇性抵消是另一个问题。稿件没有将固定阶结论直接升级成 bulk 自然边界结论。[interface reference omitted]

因此，本次审计的重点不是最后一句“稠密奇点推出自然边界”，而是：

\[
\boxed{\text{实际首项振幅}}
\quad+\quad
\boxed{\text{所有需要导数的绝对尾和界}}.
\]

---

## 二、模型、归一化和算术：未发现错误

### 2.1 没有把研究对象换成更容易的对象

稿件研究的仍是完整 bulk susceptibility，而不是 diagonal susceptibility，也不是只研究 offsite 部分。公式

\[
\mathcal X
=
1-\mathcal M^2
+
2\mathcal M^2\sum_N T_N
\]

保留了原点项与完整非原点贡献。低温零场响应也明确按正场极限纯相解释，避免了将对称混合态的响应与纯相连通响应混淆。[interface reference omitted] [interface reference omitted]

该正场极限约定与 McCoy–Maillard 原文的式 (8)–(9) 一致。[interface reference omitted]

此外，\(\beta(s)=\operatorname{arsinh}(s)/(2J)\) 没有被假定为整个外部区域上的单值函数。最终论证只需要它在选定非轴点附近局部解析且非零。这一要求与稿件采用的局部分支论证相容。

### 2.2 双轮廓归一化经受住了检查

这里最容易产生的错误是丢掉 \(N\) 个 \(2\pi i\)，或者混淆“普通轮廓积分”和“已经归一化的轮廓积分”。

重新从角测度转换，有

\[
\frac{d\theta}{2\pi}
=
\frac{dx}{2\pi i x}.
\]

再引入 \(N\) 个辅助留数，就得到总共 \(2N\) 个归一化复积分测度。稿件使用

\[
\frac{(2\pi i)^{-2N}}{N!}
\]

与这项计数一致。Tracy–Widom 的 Appendix A 确实同时包含归一化角测度和归一化辅助留数，不能只抓取正文印出的 prefactor，而忽略这两次转换。[interface reference omitted]

我也重新核算了引理 2.1：

\[
\operatorname{Res}_{x=z}\frac1{D(x,y;s)}
=
\frac{2z^2}{1-z^2}.
\]

在 \(x=0\)，

\[
D(x,y;s)^{-1}=-2x+O(x^2),
\]

确实消去了倒数分子中的表面极点。条件 \(|z|<r<1\) 则保证逐个取留数时，其他 pair/product 极点不会被意外收入轮廓。[interface reference omitted]

完整 pair 的恒等式

\[
P_{ij}
=
-\frac{(y_i-y_j)^2z_i z_j}
{y_i y_j(1-z_i z_j)^2}
\]

也由色散关系相减得到。后续关于端点和分支点的估计必须使用这个完整表达式；不能在两个单独 Schur 因子分别变坏时，仍把它们当作独立有界因子。

### 2.3 “唯一首次出现”的循环域论证成立

这里检查了三个不同命题，而不只是检查 Nickel 方程有解。

**第一，排除更低偶数阶。** 若偶数 \(n<2p\)，则 \(p\nmid n\)。循环域交给出

\[
\mathbb Q(\zeta_p)\cap\mathbb Q(\zeta_n)=\mathbb Q.
\]

而稿件的迹计算说明 \(2c\) 不可能为有理数：若其为有理数，则

\[
2c=-\frac1d<0,
\]

与所选角度给出的 \(2c>0\) 矛盾。

**第二，排除同阶其他余弦对。** 基

\[
1,u_1,\ldots,u_d
\]

之间唯一的有理关系方向是

\[
1+\sum_j u_j=0.
\]

比较两个余弦对最多涉及四个非恒定位置；\(d\ge5\) 保证存在零系数位置，迫使关系倍数为零。这正是 \(p\ge11\) 的实质作用，并非装饰性条件。

**第三，排除分支相位为单位根。** 对

\[
w=u_a+u_b-2
\]

有

\[
\operatorname{Tr}(w)=-2d-2.
\]

若 \(w=\xi+\xi^{-1}\) 且 \(\xi\) 是单位根，所有实共轭都应位于 \([-2,2]\)，迹不可能小于 \(-2d\)。这给出了后续 microcore 所需的非共振性。[interface reference omitted]

resultant 论证随后确实给出对**所有** \(N\) 成立的指数分离界，而不是只对某个子序列成立。[interface reference omitted]

---

## 三、首项奇异性：关键符号、相位和拼接均未被击穿

### 3.1 实际均角留数的符号是正确的

局部均角变量满足

\[
Y=e^{-Nc_0\varepsilon+iv},
\]

因此

\[
Y=1
\quad\Longrightarrow\quad
v=-iNc_0\varepsilon.
\]

向下闭合是顺时针方向，而

\[
\partial_v(1-Y)=-i
\]

在极点处成立。因此所得系数是

\[
\frac{-2\pi i}{-i}=+2\pi.
\]

这里没有发现漏掉负号或 \(i\) 的问题。[interface reference omitted]

另一个重要核查是：实际取到 \(Y=1\) 留数后，

\[
N(A_0+bc_0)
=
\frac{2N\sin\theta_*}{\sin\beta}
=
Q.
\]

人为引入的评价半径参数 \(c_0\) 从主振幅中消失。这是一个很有用的一致性检查；如果主振幅仍依赖任意轮廓半径，才会构成严重警报。

### 3.2 没有使用错误的联合绝对支配

这是我重点攻击的方向之一。

在形式缩放后的联合均角—形状积分中，高阶 \(Z\)-核存在随形状半径移动的 ridge。**先取绝对值再把整个联合积分用作 dominated convergence 主函数，会失败。**

v7 没有这样做。它先在真实固定矩形上进行均角变形并取留数，再对受约束形状积分作极限。附录 B 也明确区分了这两种积分次序。[interface reference omitted]

取留数后的径向次数重新核算为

\[
R^{N^2-2}(1+R^2)^{-N^2/2}
\sim R^{-2},
\]

因此得到可积尾部。这里维数、Vandermonde 次数和分母次数彼此吻合。

### 3.3 形状周期的非零性不是数值猜测

对

\[
a_0=\frac{N^2-1}{2},\qquad k+1=\frac{N^2}{2},
\]

径向积分给出

\[
J_\beta
=
\frac{C_N}{2}
Q^{-1/2}(-id)^{-a_0}
B(a_0,1/2).
\]

我检查了：

- 零和超平面的坐标体积因子确为 \(1/\sqrt N\)；
- \(C_N>0\) 来自真实形状球面上 \(\Delta^2\) 的正性；
- 转到二次系数 \(-id\) 的过程中，所用分支与可积支配相容。

因此这里的非零性有解析依据，不依赖高维数值积分。[interface reference omitted]

### 3.4 两个首项图不仅模长相同，复相位也相同

交换 \(\alpha,\beta\) 后，主系数中所有 \(\sin\beta\) 幂的总次数为

\[
-N^2-k+\frac12+3a_0=0.
\]

消去这些幂后，剩余几何因子关于 \(\alpha,\beta\) 对称；相关幂分支也没有改变。因此可以得到

\[
L_\alpha=L_\beta,
\]

而不只是 \(|L_\alpha|=|L_\beta|\)。这排除了最危险的“两个局部图同阶但相反相位”抵消。[interface reference omitted]

### 3.5 局部计算与完整积分之间的连接没有明显缺口

v7 的处理顺序是关键：

先在双轮廓层面取只依赖 \(y\) 角的固定权，保持所有 \(x\) 积分不加权；取完 \(x\) 留数后，再仅在已分离的均角边缘把平滑 cutoff 换成硬线段；最后才移动均角轮廓。它没有让非解析角权跟着复轮廓一起移动。[interface reference omitted]

对补集，引理 4.3 也不是直接套用“非 Nickel 点光滑性”——当前点本来就是 Nickel 点。它重新分类坏配置，并使用局部凸梯度分离。

辅助参数径向次数的核算也正确：若有 \(\ell\) 个奇异因子、取 \(j\) 次参数导数，做

\[
q=\ell+j+1
\]

次分部积分后，剩余径向积分是 \(R^{-2}\) 型。[interface reference omitted]

**首项链的审计结果：没有发现确定错误；这部分能够从稿件公式中重建。**

---

## 四、加权轮廓变形：Stokes 修正没有被省略

### 4.1 同伦的合法性检查通过

稿件的变形满足

\[
\sum_i h_i\le-\frac32\tau P.
\]

于是 \(|Y|<1\)。上半圆向内移动、下半圆向外移动都会增加 \(\operatorname{Im}W\)，保护内根分支。完整 canceled pair 则去除了原来表面上的 \(1-y_i y_j\) 极点。[interface reference omitted]

这里不能单靠一句“轮廓可以变形”放行；上述三个条件分别控制了不同的危险分母。

### 4.2 耦合 Jacobian 的 rank-one 项没有漏掉

角 Jacobian 是

\[
M=D+\frac{\lambda\tau}{2N}mp'^{\,T}.
\]

由于

\[
m_i p'_i=0,
\]

矩阵行列式引理确实给出

\[
\det M=\prod_i d_i.
\]

这不是把一个稠密耦合矩阵粗暴当作对角矩阵，而是利用了支撑不交这一精确结构。

在命名指标 \(q\) 上，替换列的系数为

\[
\frac{-2\tau}{i}=2i\tau.
\]

再结合分部积分负号，得到稿件的实际 Stokes current。故

\[
T_N=F_N+K_N+S_N
\]

是带修正项的精确分解，而不是把两个分别加权的轮廓积分误认成相等。[interface reference omitted]

### 4.3 没有漏掉移动截断点的导数

\(\lambda_*=\varepsilon^{\alpha_0}\) 和粒子数阈值依赖 \(\varepsilon\)，确实是潜在危险。

但稿件先对固定的整个 \(\lambda\in[0,1]\) 积分微分，再对已微分密度切分；粒子数窗口也在逐项微分后才引入。因此不会产生所谓“遗漏的 \(\lambda_*'\) 边界项”。

---

## 五、pair 收缩和三种复参数盘：最重要的压力测试之一

### 5.1 全部 pair 都严格小于一，这个命题是假的；稿件没有使用它

在分支与端点的极限组合处，确实存在

\[
|P(y_B,1)|=|P(y_B,-1)|=1.
\]

所以不能证明一个对所有 pair 统一成立的 \(q<1\)，然后直接乘起来。

v7 使用的是分组论证：同组严格收缩，跨组允许小幅膨胀。三组中同组 pair 数至少为

\[
\frac{N^2}{6}-\frac N2.
\]

配合跨组 slack 的选择，才得到

\[
\left|\prod_{i<j}P_{ij}\right|
\le C^N e^{-\kappa N^2}.
\]

这项计数与指数预算相容。稿件也明确指出 compact 组必须先排除精确分支点。[interface reference omitted]

### 5.2 三种参数盘不能混用

我分别检查了以下三种盘，而没有把其中一个的结论直接搬到另一个上：

| 场景 | 参数盘 | 真正的保护机制 |
|---|---|---|
| 原始 \(K\) 与 transition 密度 | \(c\varepsilon\) | 所有根的原始正虚部余量 |
| 最终选定 \(F_N\) | \(c/N\) | 选定上角提供固定 anchor；下分支获得 \(P/N\) 余量 |
| 大 \(\lambda\) current | \(c\lambda_*/N^2\) | 分支余量 \(\varepsilon+\lambda P/N\)，加上 \(q\) 的 \(\lambda\)-级衰减 |

重要的是，在后两种盘中，**不能假定全部 compact 根始终留在单位盘内**。稿件允许这些根少量膨胀，并用 anchor 支付总膨胀。

在大 current 盘中，这体现在

\[
|Z|
\le
\exp(-c_q\lambda+CN\delta_s),
\qquad
\delta_s=\frac{c\lambda_*}{N^2}.
\]

由于 \(\lambda\ge\lambda_*\)，第二项可以由第一项吸收。[interface reference omitted]

原始盘的一体因子估计也保留了复参数扰动引起的实分支中心漂移：

\[
O(\varepsilon^2+t^2+|s-s_\varepsilon|).
\]

没有把最后这一项丢掉；所得可积主函数也不依赖耦合 occupancy \(P\)，因此没有在积分时把 \(P\) 错当成独立常数。[interface reference omitted]

### 5.3 命题 6.1 的阶乘预算没有算错

这一估计的基本平衡是

\[
\underbrace{N^{N/2}}_{\text{one-body}}
\cdot
\underbrace{N^{N/4}}_{\text{有界 Pfaffian minor}}
\cdot
\underbrace{\frac1{N!}}_{\text{Fredholm 归一化}}
\lesssim
C^N N^{-N/4}.
\]

异常 compact pairs 带来的额外因子，再由

\[
(CN^3(H+1))^M e^{-aM^2}
\]

控制。

混合膨胀项 \(CM\sqrt N\) 也没有被漏掉，而是通过

\[
CM\sqrt N
\le
\frac a2M^2+\frac{C^2}{2a}N
\]

吸收。否则这一段确实会有严重缺口。[interface reference omitted]

另外，pointwise assignments 只用于绝对上界；Cauchy 不等式作用于完整固定权的 \(F_N\)，并没有要求这些 assignments 随 \(s\) 解析。

**这一部分仍是高风险人工复核区，但本轮没有找到错误的盘半径、错误的内根假设或无法支付的 \(N\)-代价。**

---

## 六、高阶 Lie 微分、支撑和 coarea：未发现阶数失控

### 6.1 检查不止停在一阶公式

设

\[
D=\partial_s-\mathcal L_V.
\]

二阶展开应当包含

\[
D^2A
=
\partial_s^2A
-
2\mathcal L_V\partial_sA
-
\mathcal L_{\partial_sV}A
+
\mathcal L_V^2A.
\]

因此，任何漏掉 \(\partial_sV\)、旧系数导数或散度导数的归纳都会失败。

稿件附录 D 的五类递推操作包含这些项，并保留了光滑角权被微分产生的项。关键过滤次数

\[
m+|\mu|+|\nu|\le2j
\]

在这五种操作下是闭合的。[interface reference omitted]

我没有发现一个必然产生“每阶超过两次碰撞幂损失”的遗漏操作。

### 6.2 没有通过除以 Vandermonde 制造隐藏极点

这是另一个关键点。

稿件对未除法因式化的 numerator 求导，而不是先写成

\[
\frac{\partial N_s}{N_s}
\]

再乘回原 numerator。后者会在未选定碰撞处制造新极点。

按照现有做法，固定 \(j\) 阶求导最多改变 \(j\) 个 pair 因子，其余实际 pair 的收缩仍能保留。[interface reference omitted]

### 6.3 两种穿孔通量都有正指数

选定对角线管的通量估计为

\[
h^{2M+1-2j},
\]

完全碰撞球的通量估计为

\[
\rho^{N^2-2j-3}.
\]

在 \(N\ge N_0+2,\ j\le k\) 下，后者指数为正。更重要的是，这些极限先在固定 \(\varepsilon,N\) 下进行，而不是要求穿孔极限与边界极限自动交换。[interface reference omitted]

没有发现一个被“直接丢弃”的残余通量项。

### 6.4 混合图册没有明显漏掉耦合运动

在命题 8.1 的支撑上，移动的 true-branch 指标位于 \(m=1,p=0\) 台地，命名 current 指标位于 \(p=1,m=0\) 台地。

由此，不仅低阶数值上近似保持 occupancy，而是有关方向导数在一个开邻域中恒等为零：

\[
V\cdot\nabla P=0,
\qquad
V\cdot\nabla\!\left(P\sum_i m_i\right)=0.
\]

这使高阶操作不会偷偷重新激活耦合分支运动。

混合坐标变换的 Jacobian 也是块三角的，其 branch 块给 \(\prod b_i\)，与完整角 Jacobian 合并后得到文中写出的 hybrid measure。[interface reference omitted]

这里仍值得逐项独立复核，但不能简单指控稿件“把耦合 Jacobian 丢了”：它实际保留了该项。

### 6.5 coarea 的危险损失被算进去了

全相等附近，稿件最终保留的形状幂是

\[
L=N^2-2j-4.
\]

在最不利边界 \(N=N_0+2,\ j=k\)，

\[
L
=
(N_0+2)^2-(N_0^2-2)-4
=
4N_0+2>0.
\]

这个正余量是实质性的，不是只剩一个未经控制的临界幂。[interface reference omitted]

我还检查了三个常见误算方向：

**极值指标只在微分后选择。** 因而不会产生 min/max 的分布导数。

**直径 \(d\) 不等于形状半径 \(\rho\)。** 稿件使用

\[
d\le2\rho,\qquad \rho\le\sqrt N\,d,
\]

所以近碰撞区确实保留了 \(\sqrt N\) 因子。

**周期计数不等于未展开映射的多重性。** 近相等图的相位区间长度可以是 \(O(N)\)，于是两个相位积分要支付 \(O(N^2)\)；稿件现在包含该项，也没有在做完 coarea 后把同一个 \(\rho\) 再积分一次。[interface reference omitted] [interface reference omitted]

---

## 七、指数尺度与所有尾和扇区：没有找到遗漏窗口

### 7.1 Microcore 的对数展开正确

对

\[
b_N=\frac{c_*e^{-(A+4)N}}{N},
\]

有

\[
\log\!\left(
e^{C_jN^2}b_N^{(N^2-1)/2}
\right)
=
-\frac{A+4}{2}N^3
-\frac12N^2\log N
+
O_j(N^2).
\]

v7 已经保留负的 \(N^2\log N\) 项。该界的可求和性没有依赖一个错误的主项抵消。[interface reference omitted]

### 7.2 指数尺度包含没有只在“大 \(N\)”时成立

必须对每个有限 tail 阶都满足

\[
2\rho_N\le b_N/8,
\qquad
\delta_N\le b_N/16.
\]

如果某个低阶 \(N\) 的支撑几何不满足这个条件，不能靠“增大估计常数”修复。

稿件通过 \(\Gamma_*\) 明确要求这些包含对所有 \(N\ge N_0+2\) 成立；这与“仅把有限项的数值上界吸收到常数中”是不同操作。[interface reference omitted] [interface reference omitted]

### 7.3 \(e^{CN^3}\) 没有被假装成多项式

近碰撞区的确可能出现

\[
e^{CN^3}.
\]

稿件没有将它降格为 \(N^{C_j}\)，而是使用

\[
e^{CN^3}
(2e^{-BN})^{N^2-2j-4}
\]

吸收它。先确定 \(C\)，再选 \(B\)，这个依赖顺序是必要的；现有附录 E 没有显露循环选择。[interface reference omitted]

### 7.4 十三个扇区逐项回查

我没有仅凭附录 G 的覆盖表认定“已覆盖”，而是把每行回接到实际估计机制：

| 扇区 | 实际控制机制 | 本轮结果 |
|---|---|---|
| W1 超高阶原始积分 | matched pairs、原始盘、阶乘 | 未发现漏失代价 |
| W2 最终选定 \(F_N\) | anchor、\(c/N\) 盘、compact 匹配惩罚 | 未发现结构性断点 |
| W3 高阶 \(K\) 与小 current | 原始 \(c\varepsilon\) 盘、\(e^{-\kappa N^2}\) | 预算相容 |
| W4 全分支 microcore | resultant 间隙、单相冻结、简单 \(Z\) 核 | 未发现幂发散 |
| W5 全分支远区 | rational weights、极值对 coarea | 未发现额外 \(\varepsilon^{-a}\) |
| W6 全分支近相等区 | 指数 anchor、正碰撞幂 | cubic 代价可支付 |
| W7 中间阶左 compact | 固定 \(Z\) 模间隙 | 单相积分足够 |
| W8 中间阶 mixed | 分离的 compact/branch 斜率 | 所选 measure/Jacobian 相容 |
| W9 中间阶全右 compact | 严格凹性、实角 rational atlas | 近远区衔接相容 |
| W10 小 current 左区 | 命名台地、左根间隙 | 未发现 occupancy 漏项 |
| W11 小 current mixed | 精确保留 occupancy、hybrid calculus | 高阶结构未被击穿 |
| W12 小 current 全右区 | Hessian 小扰动、正碰撞幂 | 中间窗口足以保证小扰动 |
| W13 大 current | \(c\lambda_*/N^2\) 盘、Cauchy、anchor | 得到的界足够强 |

这些行对应稿件列出的完整 tail 分解，而不是新增或替代分区。[interface reference omitted]

### 7.5 最后求和的量级相容

令 \(H=\log(1/\varepsilon)\)。各部分的总量级分别为

\[
\begin{array}{ll}
F\text{-sum}:&
\exp(O_j(\log^2H)),\\[2mm]
\text{大 current}:&
\exp(\alpha_0(j+2)H),\\[2mm]
\text{高 }N\text{ 区}:&
\exp((j+2-\kappa D^2)H+O_j(\sqrt H)),\\[2mm]
\text{中间区}:&
\exp(O_j(\sqrt H\log H)),\\[2mm]
\text{超高区}:&
\exp(-cH^2+O_j(H)).
\end{array}
\]

选择

\[
\alpha_0(k+2)<\frac12,
\qquad
\kappa D^2>k+2
\]

后，它们都小于主尺度 \(e^{H/2}=\varepsilon^{-1/2}\)。有限集合 \(0\le j\le k\) 可以共用一组常数和一个充分小的 \(\varepsilon_0\)。[interface reference omitted]

这里没有发现把只对 \(N\le D\sqrt H\) 成立的

\[
\varepsilon e^{CN}\to0
\]

偷用于全部粒子阶的情况。

---

## 八、独立计算结果及其严格边界

本轮追加的计算不是简单复述论文公式，但其证据强度也不能夸大。

| 检查 | 覆盖范围 | 结果 |
|---|---|---|
| 循环域同阶唯一性 | \(11\) 至 \(101\) 的全部 22 个素数，2,100 个允许角对；整数向量精确算术 | 未发现额外余弦对 |
| 二粒子归一化 | 三个实外部点、一个复外部点；独立 full-site 积分对比 \(f_{00}^{(2)}+2T_2\) | 最大相对差约 \(5.3\times10^{-16}\) |
| 交换首项系数 | 五组 \((p,a,b)\)，90 位算术 | \(L_\alpha/L_\beta-1\) 的模不超过约 \(2.3\times10^{-87}\) |
| 从完整密度提取 \(K_\beta\) | \(N=22\)，三个逐渐缩小的形状尺度 | 随尺度缩小收敛；最小尺度误差约 \(5.3\times10^{-21}\) |
| 原始下半圆完整 pair | 三组点，各 \(600\times600\) 网格 | 未发现违反原始半圆上界的样本 |

独立 full-site 二粒子检查使用的是 Boukraa 等式 (5)–(9) 对应的角积分，而不是对稿件的同一积分做两次相同实现。[interface reference omitted]

**这些计算没有验证无限尾和估计。** 同阶余弦枚举不代替循环域交对更低阶的排除；浮点求积没有区间误差证书；pair 网格不覆盖全部变形轮廓和复参数盘；局部密度检查也不等于数值计算完整 \(T_{22}\) 的第 241 阶导数。

TeX 另已成功独立编译为 34 页 PDF，文本差异检查未见实质性正文冲突。这也只是文件一致性检查，不是数学证明检查。

---

## 九、哪些地方仍应保留警戒，哪些不能误报为漏洞

### 最值得进一步展开的数学接口

**命题 6.1 与引理 7.2 的统一域和紧致性估计。**  
这里应让读者能够明确追踪：组的闭包、分支选择、复参数盘、同组严格常数，以及最多 \(j\) 个被改变 pair 因子的统一界。本轮的结构核查没有发现矛盾，但这里是最不适合凭一句“由紧致性显然成立”快速放行的地方。

**命题 8.1–8.2 与附录 D 的实际高阶密度。**  
抽象的两幂损失归纳是相容的；风险在于具体应用是否始终保留完整 measure、台地支撑和冻结恒等式。公开版本加入一份完全展开的二阶计算，以及实际 density 如何落入一般归纳的对照，会显著降低复核中的误读风险。

这两点是对可复核性的建议。**本轮没有证据把它们标成“命题为假”，也没有证据声称必须新增某个数学假设才能修复。**

### 未能核验的溯源范围

本轮收到的是 `.tex` 和 `.pdf`，没有收到稿件提及的独立 checkpoint v38 历史 audit packet。因此，历史 source mapping、过去审计意见及历史文件哈希链没有被核验。稿件本身也承认，这类记录不构成数学命题为真的证据。[interface reference omitted]

### 不应再当成 v7 当前漏洞的攻击

“联合均角—形状绝对支配”“直接移动平滑角权”“丢弃 Stokes 项”“在大参数盘中假定全部根仍在单位盘内”“除以 Vandermonde”“对后切分的 \(\lambda_*\) 求导”“coarea 后重复积分半径”，这些操作确实会毁掉证明。

**但它们不是 v7 当前采用的操作。** 将这些旧风险列出来不等于击穿当前稿件；必须指出当前具体哪一步又隐含地使用了它们。本轮没有找到这样的具体位置。

---

## 十、最终判断

定理 9.2 的最后逻辑是正确的：若首项系数非零、所有需要的尾导数都是 \(o(\varepsilon^{-1/2})\)，则

\[
\mathcal X^{(k)}(s_\varepsilon)
=
4\mathcal M^2(s_*)L_\beta\varepsilon^{-1/2}
+
o(\varepsilon^{-1/2})
\]

不能与局部全纯延拓相容。每个选定点的导数阶可以不同，常数可以依赖该点；稠密性论证不要求它们对素数一致。坐标轴点也不需要另做非零振幅计算，因为其任何邻域都包含所选非轴奇点。[interface reference omitted]

**所以，本次敌对性审计的结果是：v7 未被击穿。** 这不仅是“没有在数值上看到反例”：关键代数恒等式、首项留数、相位一致性、支撑保持、微分损失、coarea 次数及窗口求和都经过了针对性的核算。

同时，本轮没有完成机器形式化或全参数区间认证，整条多元解析尾和技术链仍保留人工审读的不确定性。**最准确的表述是“在上述明确覆盖的审计方向中，未检出致命错误”，而不是“自然边界定理已经因这份审计而获得独立认证”。**
