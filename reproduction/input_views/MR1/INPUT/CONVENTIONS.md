# 对象、选点与量词

## 归一化约定

定义 \(S(s)=s+s^{-1}\)，
\[
D(x,y;s)=S(s)-\tfrac12(x+x^{-1})-\tfrac12(y+y^{-1}).
\]
对偶数 N，候选 offsite 形状因子采用普通正向轮廓及显式归一化测度：
\[
T_N(s)=\frac1{N!}\oint\cdots\oint
\frac{X^{-1}+Y^{-1}}{(1-X)(1-Y)}
\prod_{i<l}\frac{x_i-x_l}{1-x_ix_l}\frac{y_i-y_l}{1-y_iy_l}
\prod_{i=1}^N\frac{dx_i\,dy_i}{(2\pi i)^2D(x_i,y_i;s)},
\quad X=\prod_i x_i,\quad Y=\prod_i y_i.
\tag{D0}
\]
外部芽与物理对象的待核对接口是
\[
\mathcal X=1-\mathcal M^2+2\mathcal M^2\sum_{N\ge2,\ N\text{ even}}T_N.
\tag{BULK}
\]
在 I1 中根据 E1 和归一化角测度独立核对这个接口，不以本文件的印刷作为证明。本文约定的每组双测度贡献 \((2\pi i)^{-2}\)；跨文献比较要同时说明归一化轮廓符号、原点项及振幅重数。

## 留数约化候选接口

\[
W(y;s)=S(s)-\tfrac12(y+y^{-1}),\quad
z=W-\sqrt{W^2-1},\quad R(y;s)=\frac{2z^2}{1-z^2},\quad Z=\prod_i z_i.
\]
z 从低温内根延拓，不能逐点任意重选平方根。先选择合法原始圆周，使 \(|z(y;s)|<r<1\)，再考虑留数及变形。
\[
T_N=\int\Omega_{N,s},\qquad
\Omega_{N,s}=\frac1{N!}\frac{Z^{-1}+Y^{-1}}{(1-Z)(1-Y)}
\prod_{i<l}P_{il}\prod_i R(y_i;s)\frac{dy_i}{2\pi i},
\tag{R0}
\]
\[
P_{il}=\frac{z_i-z_l}{1-z_iz_l}\frac{y_i-y_l}{1-y_iy_l}
=-\frac{(y_i-y_l)^2z_iz_l}{y_iy_l(1-z_iz_l)^2}.
\tag{PAIR}
\]
R0、PAIR 的代数、留数符号以及连续留数过程中其他极点是否被穿过均须重建。后一个完整配对表达式是候选消奇接口；不能先分别取两个可能奇异的 Schur 因子极限。

## 固定点族

取素数 \(p\ge11\)，整数 \(0<a<b<p/4\)，令
\[
\alpha=2\pi a/p,\quad\beta=2\pi b/p,\quad
c=(\cos\alpha+\cos\beta)/2,\quad
\theta_*=\arccos c\in(0,\pi/2),\quad s_*=e^{i\theta_*},
\]
\[
N_0=2p,\quad k=N_0^2/2-1,\quad s_\varepsilon=(1+\varepsilon)s_*,\quad
\theta_B=\arccos(2c-1),\quad \xi=e^{-i\theta_B}.
\]
I2 要证明所需算术性质：该点族稠密于第一象限弧；首次偶数 Nickel 阶为 N0；相应无序余弦对唯一；\(\xi\) 是代数的非单位根，存在固定 A>0 使 \(|1-\xi^N|\ge e^{-AN}\) 对所有正整数 N 成立。迹、稀疏圆分关系与非零整数 resultant 是候选工具，不是已核验结论。

## 量词与微分

先固定 (p,a,b)，从而固定 N0、k。允许常数依赖该点和有限阶 j≤k，不要求对所有素数统一常数。然后选择各常数和一个 \(\varepsilon_0>0\)，最后要求对全部 \(0<\varepsilon<\varepsilon_0\) 及其规定窗口中的**所有偶数 N**成立。

\(T_N^{(j)}\) 指全纯 s 导数；沿径向 \(d^j/d\varepsilon^j=s_*^j\partial_s^j\)。在中心 \(s_\varepsilon\) 选定 \(r=e^{-c_0\varepsilon}\) 后，Cauchy 盘和 s 微分期间保持该 r 固定。分割尺度、实角权重、粒子阶窗口以及 \(\lambda_*\) 均在该次求导中固定；先对完整表达式求导，再按当前 \(\varepsilon\) 分窗。

\(\beta\) 同时是物理逆温度传统记号和点族角名；上下文容易混淆时将后者写成 \(\beta_{\rm ang}\)。\(P=\sum p(\theta_i)\) 表示占据数，\(P_{il}\) 才是配对因子；不要混用。以下 \(B\) 可作分支区标签，也可作 \(\rho_N=e^{-BN}\) 的常数，须在正文中区分。
