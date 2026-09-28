# 输出、状态及冻结

## 必需文件

全部写入与 INPUT 分开的 `RUN_OUTPUT/`；可以附加自己的证明文件、源码和实际输出。

| 文件 | 内容 |
|---|---|
| `RESULT.md` | 结论、外部前提、实际完成范围、最小未闭合接口、停止原因。明确尾项重建与完整自然边界是否分别完成。 |
| `DERIVATION.md` | 可检查的本次数学推导；可作为总索引指向其他本次证明文件。所有 25 节点均有证据或明确缺口位置。 |
| `OBLIGATIONS.json` | I1–I6、T1–T6、W1–W13 各一次；机器可读的状态、依赖和本次证据位置。 |
| `COVERAGE.md` | 实际微分后域的完整覆盖、支撑、每项密度如何归属，以及 W1–W13 或等价替代映射。 |
| `CONSTANTS.md` | 常数选择次序、允许依赖、N/ε/λ 的量词、几何包含、有限低阶处理。 |
| `RUN_RECORD.json` | 见下列字段。记录声明，不把自报状态当独立认证。 |
| `ACTION_LOG.jsonl` | 实际重要读写、命令、计算、输入验证、偏离的简洁动作日志。补记或合并记录必须明示；不伪装成系统级完整审计。 |

代码不是必需的；若用于论证或校准，则连同实际输出交付。自编代码必须能区分解析推导、严格误差控制和浮点诊断。不要塞入从未运行却伪装成执行结果的文本。

## 状态

`scope` 三键：`exterior_analyticity`、`tail_estimate`、`natural_boundary`。取值为 `proved | conditional | unresolved | disproved`。相对 E1–E3 的证明可以记 proved；额外未证专用前提必须记 conditional。TAIL 被反证不自动意味着自然边界被反证。

`outcome`：

- `CLAIMED_TAIL_PROOF`：I1、I2、I4、I5，T1–T6、W1–W13 均已完成，外部全纯性及完整 TAIL 已证。允许 I3、I6 尚未闭合。仅对特定有限几个点或局部图表完成不满足此标签。
- `CLAIMED_FULL_PROOF`：全部节点、三项 scope 已证，没有影响目标的未闭合缺口。
- `CLAIMED_DISPROOF`：外部全纯性或完整自然边界命题有实际反证。候选方法、局部引理或一个充分尾界的失败不满足此标签。
- `PARTIAL`：其他实质性进展，包括发现路线障碍或条件证明。
- `INPUT_BLOCKED`：确有输入/工具障碍，记录实际原因；数学困难不要改叫输入障碍。

`method_status`：`reconstructed | partial | obstruction_found | not_started`。采用等价替代路线后成功，可用 reconstructed，但须记录替换。发现原路线错误后修复并达成原目标，也须保留错误及修补记录。

节点状态：`proved | conditional | unresolved | refuted`。这里 refuted 可以指该候选节点的局部反例，与全链反证严格区分。条件推论在前提未闭合时，不能给完整自然边界节点 I6 标 proved。替代覆盖可以将相应 W 行标 proved，并指向等价域映射及新证明。

## JSON 格式

工具 `init` 会生成格式完整、所有节点未解决的模板。只根据本次实际工作更新，不必手工重建行政结构。

RUN_RECORD 的字段：

- `schema="ising-mr1-run-v1"`, `phase="MR1"`, 唯一 `run_id`（ASCII 字母、数字、下划线、连字符），`model_or_service`，`started_utc`，`finished_utc`。
- `outcome`、`scope`、`method_status`。
- `target_preserved`：三个 scope 各自的布尔值。缩小目标且未恢复时不能仍记 true。
- `input_manifest_sha256`、`input_verification`：真实输入验证记录。init 自动填写当时的 manifest 哈希。
- `isolation`：`network`、`filesystem`、`memory_and_context` 三个非空观察说明。unknown 是允许的，不得捏造隔离。
- `allowed_method_exposure`：已提供的方法层及实际阅读情况。
- `prior_exposure`、`prohibited_comparison_material_seen`（true/false/"unknown"）。后者不包括已声明的本包蓝图。暴露不强迫把已证明的数学改为假，但会降低复现独立性，必须如实保留。
- `deviations`、`route_changes`：字符串列表；无则 []。变化需指出是等价补充还是改变目标。
- `logging_limitations`、`resource_limits`、`termination_reason`：非空文本；不知则明确 unknown。不要编造 token 用量、时间预算或系统日志完整性。
- `additional_assumptions`、`remaining_gaps`：对象列表；每项格式为 `{"id":"X1","statement":"精确前提或缺口","affects":["tail_estimate"]}`。affects 可包含上述三个 scope 的一个或多个。E1–E3 不属于 additional_assumptions；新增未证专用前提属于。

OBLIGATIONS 的格式为 `{"schema":"ising-mr1-obligations-v1","nodes":[...]}`。每个节点：

```json
{
  "id": "I5",
  "status": "unresolved",
  "evidence": [{"path": "DERIVATION.md", "anchor": "I5"}],
  "dependencies": ["I2", "I4", "T6"],
  "assumptions": ["E1"],
  "note": "写实际证据或最小缺口，不以蓝图为证明。"
}
```

证据路径相对 RUN_OUTPUT，必须是真实文件；anchor 为明确的节名、定理号或行号。依赖 ID 可用 25 个节点、E1–E3 或已声明的额外假设 ID。assumptions 只列 E1–E3 和额外假设。只把**数学依赖**填入 dependencies：不要把“所属组”和“被哪个组总结”双向填入而人为制造循环。若叶节点彼此共享估计，在正文另设引理并指向其证据，不需要让概览节点与叶节点相互证明。

工具会拒绝已声明的依赖循环、proved 节点依赖未闭合节点、proved 结果仍带影响它的额外假设/缺口等明显记录矛盾。这不是证明检查器，也不会判断是否漏填了真正依赖，或锚点内容是否真的证明了结论。

ACTION_LOG 每行一个 JSON 对象，包含非空字符串 `time_utc, action, target, result, access_class`。access_class 取 `allowed_input | own_output | runtime | deviation`。不知道事件时间时写 unknown；工具初始化时间只是环境时钟，并非受信时间戳。记录足够还原输入/输出与实际执行动作即可，无需记录私有内部思考。

## 命令

从 INPUT 目录运行，Python 3.9+、标准库即可：

```text
python -B tools/packet_tools.py verify
python -B tools/packet_tools.py init --results ../RUN_OUTPUT --run-id ISING-MR1-你的唯一ID
python -B tools/packet_tools.py validate --results ../RUN_OUTPUT
python -B tools/packet_tools.py freeze --results ../RUN_OUTPUT --archive ../ISING_MR1_RUN_FROZEN.zip
```

先把 verify/validate 的真实输出存到 RUN_OUTPUT（可选文件名 `input_verification.json`、`administrative_validation.json`）。最后一次 freeze 会再验输入、快照全部结果文件、核对声明的 manifest、保留逐文件哈希并生成 `.zip.sha256`。工具拒绝覆盖已有归档/回执；重试用新路径并说明原因。

冻结元数据在归档根目录，结果在 `RESULT/`，另附本次输入 manifest。工具不将其最后打印的成功消息回写结果目录；无需在冻结之后为补日志而修改原始结果。所有补充必须在后续独立阶段记录。

若实际无法运行工具，返回已有文件并明确“未冻结”，不得伪造 `RESULT_SNAPSHOT_FROZEN`。若初次 verify 失败，工具会拒绝冻结；保持原输入、输出实际错误及诊断，等待操作者修复传输问题。冻结状态无论成功与否都不认证数学或隔离。
