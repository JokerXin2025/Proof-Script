# 嵌入式计算渲染协议

本文面向 Proof-Script 后端和协议维护者。前端实现请阅读
`Frontend-Computation-Handoff-zh.md`；SpherePaper E8 的具体模块设计请阅读
`E8-Embedded-Computation-Design-zh.md`。

`#computation` 用于把 Lean 声明与网页交互组件连接起来。页面 JSON 负责携带可追溯的 Lean
来源、稳定的组件外壳和 renderer 专用 manifest；`function.implementation` 指向同一表达式表中的
函数实现体。该实现不把 Lean 编译器内部 IR 误当作稳定的
JavaScript 或 WebAssembly ABI。

## 数据契约

组件 `schemaVersion` 独立于页面 schema，当前为 `1.0.0`。renderer 必须：

1. 拒绝不支持的组件 major version。
2. 按完整 `renderer` ID 分派，例如 `proof-script/e8-root-explorer-v1`。
3. 校验该 renderer 自己定义的 `payload` schema。
4. 用 `function.declaration` 和 `function.type` 展示来源，用 `expression`、`implementation` 与 `expressions` 做审计、索引或静态分析。
5. 不直接执行页面提供的任意脚本，不把 `payload` 字符串拼接进 DOM。
6. renderer 不可用、JavaScript 被禁用或 manifest 校验失败时显示 `payload.fallback`。

## 执行后端

建议 renderer 为每个计算组件显式选择以下后端之一：

| 后端 | 用途 | 页面产物 | 信任边界 |
| --- | --- | --- | --- |
| `table` | 有限输入、教学演示、离线文档 | 编译期生成或核验的输入输出表 | renderer 只查表 |
| `wasm` | 纯函数、大量客户端计算 | 带 hash 的 Wasm resource、导出名、编解码 schema | 在 Worker 中限制内存和时间 |
| `rpc` | 依赖大型 Lean 环境或服务端证明检查 | endpoint capability、请求/响应 schema | 服务端重新校验所有输入 |
| `declarative` | 投影、公式、状态机等专用可视化 | renderer 专用参数 | 不执行通用代码 |

Proof-Script 已完成 `proof-script-json-v1` 的 Wasm 可行性实现。Lean 侧公共函数
`ProofScript.Computation.invokeJson` 接受 `α → Except String β`，通过 `FromJson α` 与
`ToJson β` 在 Wasm 内完成解析、类型校验、计算和编码。当前仍是手工 bundle Spike，尚未由
`#computation` 自动生成和写入页面 resource。正式 bundler 应把二进制写入
`.Proof-Script/resources/wasm/`，以 `$resource` 携带 path、hash、mediaType 和 encoding。

### proof-script-json-v1

Wasm 边界输入和输出都是 UTF-8 JSON。成功响应：

```json
{"ok": true, "value": {}}
```

失败响应：

```json
{
  "ok": false,
  "error": {"code": "invalid-input", "message": "..."}
}
```

稳定错误代码：

- `invalid-json`：输入不是合法 JSON。
- `invalid-input`：JSON 无法解码为入口函数的输入类型。
- `computation-error`：入口函数返回 `Except.error`。

当前 C/Wasm ABI 导出 `proof_script_init`、`proof_script_alloc`、`proof_script_free` 和
`proof_script_invoke`。调用方先提供输出缓冲区；若返回长度大于容量，应按该长度重新分配并再次
调用。昂贵计算的正式实现应改为由 Wasm 管理单次结果句柄，避免仅为扩容重复计算。

## 编译期入口登记

`#computation` 现已执行阶段 3 登记流程：

1. 解析 Lean 声明并要求恰好一个显式、非依赖输入参数。
2. 接受 `α → β` 或 `α → Except String β`；纯函数自动通过 `Except.ok` 提升。
3. 编译期合成 `FromJson α` 和 `ToJson β`，缺失时直接拒绝页面模块。
4. 在原模块中生成稳定的 `String → String` wrapper，调用
   `ProofScript.Computation.invokeJson`。
5. 写入 `.Proof-Script/computations/pending/` 入口 manifest。
6. 页面组件写入 `execution.backend = "wasm"`、`status = "pending"`、bundle ID、entry、
   wrapper 和 manifest 路径。

当前限制：入口不能是 universe-polymorphic 函数，不能有隐式输入或依赖输出。阶段 4 bundler
已能消费 pending manifest；阶段 5 finalizer 也已能把页面中的 `pending` 替换为内容寻址 Wasm
resource。

## 多入口 Bundle

阶段 4 bundler 位于 `scripts/build-computations.mjs`。它执行：

1. 递归扫描 `.Proof-Script/computations/pending/*.json`。
2. 按 `bundleId` 分组，并要求当前一个 bundle 只属于一个 Lean 模块。
3. 定位 `.lake/build/ir/<module>.c` 和 `.setup.json`。
4. 按 Lean `Name.mangle` 规则计算 wrapper C 符号，并验证 C IR 中确实存在。
5. 加入 `ProofScript.Computation.Json` support C IR。
6. 生成按 entry ID 分派的 C dispatcher。
7. 用 Emscripten 将多个 wrapper 和一份 Lean runtime 链接为共享 Wasm。
8. 实例化 bundle 并执行 unknown-entry 自动 smoke test。
9. 写出 `bundle.mjs`、`bundle.wasm` 和含 SHA-256 的 `bundle.json`。

运行方式：

```sh
source "$HOME/Developer/emsdk/emsdk_env.sh"
PROOF_SCRIPT_LEAN_WASM_PREFIX=/path/to/lean-wasm-prefix \
  node /path/to/Proof-Script/scripts/build-computations.mjs
```

dispatcher ABI 在原有参数前增加 entry ID：

```c
uint32_t proof_script_invoke(
  uint32_t entry_ptr,
  uint32_t entry_len,
  uint32_t input_ptr,
  uint32_t input_len,
  uint32_t output_ptr,
  uint32_t output_capacity
);
```

当前采用 `module-local` linking，只自动链接声明模块与 JSON support 模块。入口引用其它项目运行时
模块时，链接器会明确报告 undefined symbol；项目级依赖闭包将在后续优化中实现。

## Finalize

`scripts/finalize-computations.mjs` 将 module + Wasm 按组合 SHA-256 发布到：

```text
.Proof-Script/resources/computation/<bundleHash>/
```

它验证 pending/bundle/page entry 一致性、Wasm hash 和内容寻址碰撞，随后将页面 execution 更新为
`ready`，写入 manifest/module/wasm 三个 `$resource`。页面和 finalized index 使用临时文件后原子
rename。前端接入详见 `Frontend-Computation-Handoff-zh.md`。

## 浏览器实现流程

1. 页面加载器按照页面顺序读取 component envelope。
2. 遇到 `computation` 时先渲染标题和 fallback，避免 hydration 前空白。
3. renderer registry 按完整 ID 动态加载受信任模块，未知 ID 保留 fallback。
4. 用 JSON Schema 校验 `payload`，并检查函数类型是否符合 renderer 预期。
5. 将昂贵计算放入 Web Worker；设置输入大小、运行时间、内存和输出大小上限。
6. 以结构化状态更新视图，不使用 `eval`、`new Function` 或未经清理的 `innerHTML`。
7. 在界面同时显示计算结果、Lean 声明链接和“计算示例不等于一般性证明”的边界说明。

建议的 TypeScript 分派接口：

```ts
type ComputationRenderer = {
  payloadSchema: object;
  mount(host: HTMLElement, value: ComputationValue, signal: AbortSignal): Promise<void>;
};

const computationRenderers = new Map<string, () => Promise<ComputationRenderer>>([
  ["proof-script/e8-root-explorer-v1", loadE8RootExplorer],
]);
```

## E8 Demo renderer

`proof-script/e8-root-explorer-v1` 应实现四个联动视图：

1. 根族选择器调用表后端，展示整数族 `112`、半整数族 `128` 和总数 `240`。
2. 坐标检查器按 manifest 中的精确规则生成根，使用有理数而非浮点数计算范数平方 `2`。
3. 投影视图允许切换 Coxeter 平面和坐标投影，按根族着色，并强调投影不是八维格子本身。
4. 密度视图允许把半径拖到 `sqrt(2)/2` 两侧，联动展示 separation 证书有效性及
   `vol(B^8(sqrt(2)/2)) / covolume(E8) = pi^4/384`。

有限枚举说明 240 个最小根的结构；非零格点不存在更短向量仍由 `E8_norm_lower_bound` 等 Lean
定理承担。renderer 应始终显示这一区别，并链接 manifest 的 `formalDeclarations`。
