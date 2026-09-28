# 二维 Ising 完整体磁化率自然边界：候选证明与审查材料

**v0.1-rc2，供公开数学审查的候选稿，2026-09-28。作者：Dehao Lin，School of Physics, Sun Yat-sen University。**

[论文](paper/manuscript.pdf) · [TeX 源码](paper/manuscript.tex) · [两页专家简报](docs/expert_brief.pdf) · [English](README.md)

## 对象与主张

本仓库呈现一份 AI 辅助候选证明，研究低温纯相外部解析芽对应的无限正方晶格、零场、各向同性**完整体磁化率**，包括所有格点间距及完整偶数粒子展开。论文声称单位圆是自然边界；这一主张尚无独立人类或证明助手认证。[精确主张](CLAIMS.md) · [外部前提](provenance/EXTERNAL_PREMISES.md)。

## 历史缺口

Nickel 给出了稠密的固定 form-factor 奇性结构。Orrick、Nickel、Guttmann、Perk 根据振幅随粒子阶的变化提出不抵消证据，并明确区分于证明。Tracy–Widom 有固定偶阶的非 Nickel 光滑性结果，以及对角磁化率和 Toeplitz 和的严格非抵消先例。本稿针对的严格论证缺口是无限高阶粒子尾和的控制；固定阶奇点稠密本身不排除求和抵消。[归属与先行工作](provenance/PRIOR_ART.md)。

## 两条承重估计

对正文 §3 每个固定选定点 $s_*$，令 $N_0=2p$、$k=N_0^2/2-1$、$s_\epsilon=(1+\epsilon)s_*$。论文声称

$$
\partial_s^k T_{N_0}(s_\epsilon)=2L_\beta\epsilon^{-1/2}+o(\epsilon^{-1/2}),\qquad L_\beta\ne0,
$$

$$
\sum_{\substack{N>N_0\\N\ {\rm even}}}|\partial_s^j T_N(s_\epsilon)|=o(\epsilon^{-1/2}),\qquad 0\le j\le k.
$$

第一条提供非零奇异首项；第二条使整个高粒子数尾和不足以抵消它。常数允许依赖固定点和有限阶 $k$。这两条是需要核查的证明主张。

## 证明结构

稠密且首次阶唯一的点族导向**整个 form factor** 的非零首项；精确加权轮廓分解 $T_N=F_N+K_N+S_N$ 导向所有高阶偶数项的微分控制。两路结合低阶有界性和外部正规收敛，在稠密边界点排除抵消，推出所声称的自然边界。[证明路线](docs/PROOF_GUIDE.md)；正文 §§3–9、附录 B–G。

## 候选贡献与已有先例

“首项发散、余和受控”的结构不是本项目首创；Tracy–Widom 的对角磁化率工作已有先例。其 Toeplitz 工作也已有分组、Vandermonde、轮廓划分和 Hadamard／阶乘预算。本稿候选技术贡献是这些方法在**完整体磁化率中的具体实现**，包括选点、完整首项拼接、加权轮廓、保护圆盘及高阶尾项/coarea 估计。有限文献检索不能提供穷尽的优先权核准。

## 状态与局限

- rc2 保持 v8 / rc1 数学内容，修改学术归属、版本和公开呈现。
- AI 敌对审计发现并促成了实际修补；各报告只对应其输入版本及检查范围，不是同行评审或当前稿件认证。
- 三次无方法提示 CR0 均为 `PARTIAL`，完整自然边界复现为 **0/3**。第一、第三次对有限首项提出更完整主张，第二次也保留整体首项未决；三次都未完成完整尾和控制。
- 一次 MR1 获得方法蓝图后声称完成完整 TAIL，但 I3 未决、I6 条件成立；接收核查没有独立认证整条 TAIL。
- 不同点族不能直接拼接；不能把复现未完成简单归因于篇幅。会话可能共享模型先验，技术隔离未经独立核验。
- 没有独立人类专家认证、证明助手验证或完整无提示复现。有限计算不认证连续域和无限尾项。[局限](LIMITATIONS.md) · [候选状态](release/STATUS.json)。

## 如何核查

可只选择一个接口：首项及补集（§4、附录 B）；加权轮廓与配对控制（§§5–8）；高阶微分、通量与 coarea（附录 D–E）；W1–W13 完整尾和接合（§9、附录 G）。欢迎具体失效配置、未经证明的推论或一致性步骤、遗漏的相近先例；不预设完整审稿承诺。[反馈说明](CONTRIBUTING.md)。

## 审计、复现与来源

[审计索引](audits/README.md)说明历史文件名和裁决范围，原文保持不变。[版本表](audits/VERSION_LEDGER.md)、[CR0/MR1 对照](reproduction/README.md)、[来源记录](provenance/SOURCE_PROVENANCE.md)及[原始 URL 清单](provenance/V38_SOURCE_INVENTORY.json)保留负面和未完成结果。原始 v38 的 192 项完整性核对通过；189 个文本的显式来源扫描未发现外部 AI 证明仓库列为研究来源，但历史访问日志不完整，不能保证零未记录接触。本项目的 AI 推导是待核查论证，不是外部可信前提。

在仓库根目录运行 `python scripts/verify_repository.py` 和 `python scripts/reproduce.py`。依赖与命令见英文入口。[计算检查范围](checks/README.md) · [编译说明](paper/README.md) · [最终公开装配验证记录](release/FINAL_PUBLIC_VALIDATION.md)。输出写入 `.local/`，不改证据。历史发布视图与冻结原件通过散列和转换清单区分；第三方论文全文、系统日志和私人联系草稿不随公开包分发。

## 引用、作者与许可

Dehao Lin 是署名人类作者及公开联系人；生成式 AI 广泛参与研究探索、推导、写作、代码和内部审计。[作者声明](AUTHORSHIP.md) · [版本引用](CITATION.cff)。代码采用 [MIT](LICENSE)；论文及项目自撰文档采用 [CC BY 4.0](LICENSE-DOCUMENTATION.md)；第三方作品保留自身权利。[第三方说明](THIRD_PARTY_NOTICES.md)。
