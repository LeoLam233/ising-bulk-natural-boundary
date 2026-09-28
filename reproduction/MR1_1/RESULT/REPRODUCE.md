# 实际运行材料与复算入口

本归档的数学推导在 `proofs/`，总索引 `DERIVATION.md`，覆盖 `COVERAGE.md`，常数 `CONSTANTS.md`。声明和依赖图在 `RUN_RECORD.json`、`OBLIGATIONS.json`。这些声明不因行政工具通过而成为独立认证。

## 输入与恢复

原上传包 SHA-256：

`ca7d857b5dc58422b9539b79807d9cbc70de0f19fe2e8c5de5a518d56aa83498`。

输入 manifest SHA-256：

`784b28dbb6b2f913b33abbf4de3dfd673115bf517e222eb3cdb7504089777149`。

实际恢复后先安全检查 ZIP 路径、重复名、链接、CRC 和清单，再运行包内 verify/init。`input_verification.json`、`initialization.json` 是当时的实际标准输出。前工作目录丢失与同一请求的上级续接上下文已在日志披露；当前文件才是交付证据。

## 实际计算

在结果目录的**新复制品**中，可用已有相应依赖的普通 Python 环境执行：

```text
python -B code/algebra_checks.py
python -B code/coupled_diagnostics.py
python -B code/self_check.py
```

第一项是精确 SymPy 代数检查，第二项是 mpmath 65 位有限配置的浮点诊断，第三项只检查当前结果结构、锚点、状态与实际输出的一致性。它们的本次真实输出分别在 `computations/algebra_checks.json`、`computations/coupled_diagnostics.json`、`computations/self_check.json`。环境版本见 `computations/runtime_inventory.json`。本次没有安装新依赖，没有联网；缺少依赖的新环境不能把未执行的诊断冒充为已执行。

`code/log_action.py` 只追加自报动作；`code/finalize_records.py` 只写本次声明账本，**不是数学证明检查器**，也不应对冻结快照原地重跑。`computations/record_generation.json` 是声明写入器的实际输出。

## 文献页检查

只使用原包提供的文献。TW PDF 的第 2、3、8、9、10 页用已有 `pdftoppm -f 页号 -l 页号 -scale-to 1800 -png ...` 本地渲染并实际查看，图像和 stdout/stderr 保留于 `reference_checks/`。机械提取文本只用于查找，不替代权威 PDF 公式。

按上级操作规范额外读取的仅为两个通用程序性文件：

`[LOCAL_PATH_REDACTED]`；
`[LOCAL_PATH_REDACTED]`。

没有执行包外辅助脚本或读取包外 Ising 证明。普通 Python 库、pdftoppm 和用于一次合同文字渲染的运行环境字体属于普通运行环境；未复制或分享字体文件。

## 行政验证与冻结

本次从原工作树 INPUT 目录执行的命令为：

```text
python -B tools/packet_tools.py validate --results ../RUN_OUTPUT
python -B tools/packet_tools.py freeze --results ../RUN_OUTPUT --archive [LOCAL_PATH_REDACTED]
```

最终 validate 的真实标准输出存为 `administrative_validation.json`。freeze 会再次验证输入、结果结构及逐文件字节，并将 `FREEZE_RECORD.json` 写在归档根目录、结果写在 `RESULT/`、附上输入 manifest，然后在归档外写 `.zip.sha256` 回执。freeze 的成功消息按包内设计不回写 RUN_OUTPUT；执行之前的最后日志是冻结意图，真正结果以归档根的工具记录及回执为准。

归档不附原始整包；重检时将原包的 INPUT 与解开的 RESULT 放在同级，从 INPUT 运行 `validate --results ../RESULT` 即可。重新计算需要复制到另一个结果目录，不要修改这份已冻结快照。行政工具不核验数学、技术隔离或时间戳真实性。
