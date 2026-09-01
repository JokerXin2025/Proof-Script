# SpherePaper E8 嵌入式计算模块设计

本文说明如何把 SpherePaper 当前的简单 `E8RootFamily → Nat` 示例升级为一个真正由 Lean/Wasm
执行、并由形式化定理解释其正确性的 E8 根系与球填充交互组件。

相关项目：

```text
/Users/zhoukexin/Proof-Script.Demo20260901
```

当前页面：

```text
SpherePaper/Geometry/E8/Definitions.lean
```

数学实现：

```text
SpherePacking/Basic/E8.lean
```

## 当前状态与目标

当前页面函数：

```lean
inductive E8RootFamily where
  | integral
  | halfIntegral
deriving Lean.FromJson, Lean.ToJson

def e8RootCount : E8RootFamily → Nat
  | .integral => 112
  | .halfIntegral => 128
```

该函数现在已经能通过新版 `#computation` 自动生成 typed JSON wrapper、pending manifest 和 Wasm
entry，但它只返回两个常数。正式新版组件应让 Lean/Wasm 实际完成：

1. 枚举 112 个整数型最短根。
2. 枚举 128 个半整数型最短根。
3. 返回全部 240 个根的精确坐标。
4. 核验每个根的范数平方为 2。
5. 按用户选择筛选根族和坐标投影。
6. 判断给定有理半径是否超过不相交阈值 `sqrt(2) / 2`。
7. 返回 E8 packing density 的精确符号数据 `pi^4 / 384`。

前端只负责状态、绘图和动画，不应硬编码 `112`、`128`、`240` 或重新实现根枚举算法。

## 页面位置

保留当前组件位置：E8 基底矩阵之后、两张静态二维投影图之前。

```text
E8 二陪集定义
→ E8 基底矩阵
→ 交互式根系/packing 计算
→ 静态投影 A/B fallback
→ 形式证明接口说明
```

这个位置能把代数定义、最短根、separation、packing radius 和 density 串成一个连续论证。

## 模块组织

### 当前 bundler 下的可工作方案

阶段 4 bundler 当前采用 `module-local` linking，只自动链接声明 `#computation` 的页面模块和
`ProofScript.Computation.Json`。因此第一版可运行实现应把计算数据类型和 `computeE8` 放在：

```text
SpherePaper/Geometry/E8/Definitions.lean
```

或让页面模块中的 wrapper 只调用同模块内定义的计算函数。否则将函数放到独立 imported module 后，
bundler 会因没有加入该模块 C IR 而报告 undefined symbol。

### 依赖闭包完善后的推荐结构

长期推荐拆分：

```text
SpherePaper/Computations/E8Roots.lean
SpherePaper/Geometry/E8/Definitions.lean
```

前者只 import `Init`、必要的 `Std` 和轻量可计算定义；后者 import 计算模块和正式数学定义，负责
页面组件及连接定理。这样可避免把大型 Mathlib 页面依赖带入 Wasm。

在 bundler 支持显式 computation dependencies 前，不应提前采用该拆分并假设它会自动链接。

## 精确数据表示

不要使用 `Array Float` 表示根。E8 根坐标只需要整数和二分之一，可以统一表示为：

```lean
inductive E8RootFamily where
  | integral
  | halfIntegral
deriving Repr, DecidableEq, Lean.FromJson, Lean.ToJson

structure E8Root where
  numerators : Array Int
  denominator : Nat
  family : E8RootFamily
deriving Repr, Lean.FromJson, Lean.ToJson
```

约定：

- `numerators.size = 8`。
- `denominator = 1` 表示整数根。
- `denominator = 2` 表示半整数根。
- 坐标为 `numerators[i] / denominator`。

整数根例子：

```json
{
  "numerators": [1, -1, 0, 0, 0, 0, 0, 0],
  "denominator": 1,
  "family": "integral"
}
```

半整数根例子：

```json
{
  "numerators": [1, 1, -1, -1, 1, 1, 1, 1],
  "denominator": 2,
  "family": "halfIntegral"
}
```

前端可以为绘图转换成 `number`，但坐标检查器和范数说明应始终显示精确分数。

## 根枚举算法

### 整数根

所有排列：

```text
(±1, ±1, 0, 0, 0, 0, 0, 0)
```

Lean 算法：

```lean
def integralRoots : Array E8Root :=
  ((List.range 8).flatMap fun i =>
    (List.range 8).flatMap fun j =>
      if i < j then
        [-1, 1].flatMap fun si =>
          [-1, 1].map fun sj =>
            -- 在 i/j 放 si/sj，其余为 0
      else []).toArray
```

计数：

```text
C(8, 2) * 2^2 = 28 * 4 = 112
```

### 半整数根

枚举 8 个符号位；负号数量为偶数：

```text
(±1/2, ..., ±1/2)
```

Lean 算法可枚举 `mask : Fin 256`，使用 bit count parity 过滤：

```lean
def halfIntegralRoots : Array E8Root :=
  (List.range 256).filterMap fun mask =>
    if evenMinusSigns mask then
      some {
        numerators := Array.ofFn fun i => if bitSet mask i then -1 else 1
        denominator := 2
        family := .halfIntegral
      }
    else none
  |>.toArray
```

计数：

```text
2^7 = 128
```

必须固定枚举顺序，以保证相同 Lean 源码产生稳定 JSON、测试 snapshot 和视觉选择索引。

## 请求协议

建议不要让一个 entry 只接收根族枚举，而使用可扩展结构：

```lean
inductive E8RootFilter where
  | all
  | integral
  | halfIntegral
deriving Repr, Lean.FromJson, Lean.ToJson

inductive E8Projection where
  | coordinates (x y : Nat)
  | coxeterPlane
deriving Repr, Lean.FromJson, Lean.ToJson

structure RationalRadius where
  numerator : Nat
  denominator : Nat
deriving Repr, Lean.FromJson, Lean.ToJson

structure E8Request where
  family : E8RootFilter := .all
  projection : E8Projection := .coxeterPlane
  radius? : Option RationalRadius := none
deriving Repr, Lean.FromJson, Lean.ToJson
```

验证规则：

- coordinate projection 要求 `x < 8`、`y < 8` 且 `x != y`。
- radius denominator 不能为 0。
- 输入大小仍由 Worker transport 限制。

`coxeterPlane` 的精确投影系数涉及代数数。第一版可以让 Lean 返回精确八维根，由前端使用固定、
经过测试的浮点投影矩阵绘图；该浮点视图必须标记为 visualization，不参与形式证书。

## 响应协议

建议：

```lean
structure E8PackingData where
  separationSquared : Nat
  maximumRadius : String
  covolume : Nat
  density : String
  densityApproximation : Float
deriving Lean.ToJson

structure E8Response where
  roots : Array E8Root
  integralCount : Nat
  halfIntegralCount : Nat
  totalCount : Nat
  selectedCount : Nat
  normSquared : Nat
  radiusAdmissible? : Option Bool
  packing : E8PackingData
deriving Lean.ToJson
```

稳定结果：

```text
integralCount = 112
halfIntegralCount = 128
totalCount = 240
normSquared = 2
packing.separationSquared = 2
packing.maximumRadius = "sqrt(2)/2"
packing.covolume = 1
packing.density = "pi^4/384"
```

`String` 字段用于精确符号显示，不应由前端重新推导。`densityApproximation` 只用于图表和辅助提示。

## 半径判断

若输入半径为非负有理数 `r = n / d`，不需要在 Wasm 中计算 `sqrt(2)`：

```text
r <= sqrt(2)/2
↔ 2 r^2 <= 1
↔ 2 n^2 <= d^2
```

因此可以纯整数计算：

```lean
def radiusAdmissible (radius : RationalRadius) : Except String Bool := do
  if radius.denominator = 0 then throw "radius denominator must be nonzero"
  return 2 * radius.numerator ^ 2 ≤ radius.denominator ^ 2
```

这避免浮点边界误判，并能直接与 separation theorem 的平方形式连接。

## Lean 入口

```lean
def computeE8 (request : E8Request) : Except String E8Response := do
  validateProjection request.projection
  let radiusAdmissible? ← request.radius?.mapM radiusAdmissible
  let integral := integralRoots
  let halfIntegral := halfIntegralRoots
  let all := integral ++ halfIntegral
  let roots := filterRoots request.family all
  return {
    roots
    integralCount := integral.size
    halfIntegralCount := halfIntegral.size
    totalCount := all.size
    selectedCount := roots.size
    normSquared := 2
    radiusAdmissible?
    packing := {
      separationSquared := 2
      maximumRadius := "sqrt(2)/2"
      covolume := 1
      density := "pi^4/384"
      densityApproximation := 0.253669507901048
    }
  }
```

组件：

```lean
#computation
  (title := "E8 の 240 根と packing density", label := "e8-root-explorer")
  "proof-script/e8-root-explorer-v2"
  computeE8
  r#"
  {
    "contractVersion": "2.0.0",
    "defaultInput": {
      "family": "all",
      "projection": "coxeterPlane"
    },
    "views": [
      "family-selector",
      "exact-coordinate-inspector",
      "projection",
      "density"
    ],
    "formalDeclarations": [
      "E8_integral_self",
      "E8_norm_eq_sqrt_even",
      "E8_norm_lower_bound",
      "E8Packing_separation",
      "E8Packing_density"
    ],
    "fallback": {
      "summary": "E8 has 240 norm-two roots and packing density pi^4/384.",
      "figures": [
        "assets/figures/e8plot_A.pdf",
        "assets/figures/e8plot_B.pdf"
      ]
    }
  }
  "#
```

payload 不再携带手工 `results.integral = 112` 等执行结果。结果必须来自 Lean/Wasm 响应。

## 形式证明连接

计算模块应逐步加入以下定理。

### 第一层：可执行不变量

```lean
theorem integralRoots_size : integralRoots.size = 112 := by native_decide
theorem halfIntegralRoots_size : halfIntegralRoots.size = 128 := by native_decide
theorem allRoots_size : (integralRoots ++ halfIntegralRoots).size = 240 := by native_decide
```

### 第二层：声音性

将 `E8Root` 转为 `Fin 8 → ℚ`：

```lean
def E8Root.toRatVector (root : E8Root) : Fin 8 → ℚ := ...

theorem enumerated_root_mem_E8
    (root : E8Root) (h : root ∈ allRoots) :
    root.toRatVector ∈ Submodule.E8 ℚ := ...

theorem enumerated_root_norm_squared
    (root : E8Root) (h : root ∈ allRoots) :
    root.toRatVector ⬝ᵥ root.toRatVector = 2 := ...
```

### 第三层：完备性

```lean
theorem enumerate_roots_complete
    (v : Fin 8 → ℚ)
    (hv : v ∈ Submodule.E8 ℚ)
    (hnorm : v ⬝ᵥ v = 2) :
    ∃ root ∈ allRoots, root.toRatVector = v := ...
```

完备性证明难度高，可以后置；UI 在它完成前应表述为“Lean 算法枚举的 240 个根”，不要声称计算
本身取代了 `E8_norm_lower_bound` 对无限格点的证明。

### 第四层：packing 对接

使用现有正式声明：

```text
E8_integral_self
E8_norm_eq_sqrt_even
E8_norm_lower_bound
E8Packing_separation
E8Packing_numReps
E8_ℤBasis_ofZLatticeBasis_volume
E8Packing_density
```

计算结果中的 `separationSquared = 2`、`covolume = 1` 和 `density = pi^4/384` 应链接这些声明，
而不是只作为未经说明的常量。

## 基底矩阵注意事项

当前 `Definitions.lean` 页面展示的 presentation basis 与
`SpherePacking/Basic/E8.lean` 中的实际 `E8Matrix` 不是逐项相同的矩阵。它们可能是同一格子的
不同基底，但交互组件不能把页面矩阵标记为“从 Lean `E8Matrix` 直接导出的值”。

新版组件应采取以下之一：

1. 直接从 Lean 的 `E8Matrix ℚ` 导出基底数据。
2. 明确标记 `presentationBasis` 和 `leanBasis`，并提供整数 unimodular change-of-basis 证书。
3. 根系 explorer 不展示基底计算，只展示两陪集根枚举，避免混淆。

第一版推荐第 3 种，后续再正式解决基底等价。

## 前端四视图

### 根族选择器

- `all`、`integral`、`halfIntegral`。
- 数量完全来自 `E8Response`。
- 切换时调用同一个 `computeE8` entry。

### 精确坐标检查器

- 显示 8 个分数坐标。
- 显示 family、范数平方 2 和 antipodal root。
- 不用 Float 判断根相等或范数。

### 二维投影

- Canvas 或 SVG 绘制。
- 两根族分色。
- 支持 hover、selection 和 `v/-v` 联动。
- Coxeter plane 使用前端固定浮点矩阵，但输入根来自 Lean。
- 明确标记“二维可视化，不是完整八维格子”。

### Density

- 用户输入有理半径或由 slider 生成有限精度有理数。
- 调用 Lean 获得 `radiusAdmissible`。
- 阈值处展示 `sqrt(2)/2`。
- 展示 `pi^4/384` 和近似值。
- 超过阈值时说明 separation certificate 不支持该半径。

## 构建流程

负责网站发布的前端/renderer pipeline 必须执行：

```sh
cd /Users/zhoukexin/Proof-Script.Demo20260901

# 1. 编译页面和计算 wrapper，且必须生成最新 C IR/setup.json
lake build SpherePaper.Geometry.E8.Definitions

# 或项目稳定后执行完整构建
# lake build

# 2. 生成多入口 Wasm
PROOF_SCRIPT_LEAN_WASM_PREFIX=/path/to/lean-wasm-prefix \
  node /Users/zhoukexin/Proof-Script/scripts/build-computations.mjs

# 3. 发布 hash 资源并回填页面 ready execution
node /Users/zhoukexin/Proof-Script/scripts/finalize-computations.mjs
```

当前 `scripts/compile_demo.sh` 只传 `-o` 和 `-i`，不会生成 bundler 所需的模块 `.c` 和
`.setup.json`，不能单独作为新版嵌入式计算的发布构建。可以继续用它验证论文模块，但计算页面还
必须通过 Lake target 产生 C IR，或专门升级该脚本以同时生成与 Lake setup 等价的构建产物。

Finalize 后再编译 `Definitions.lean` 会把页面重写为 `pending`，所以 finalize 必须是部署前最后一个
Proof-Script 数据步骤。

## 分步实施计划

### 里程碑 A：替换常数函数

- 定义 `E8Root`、请求和响应。
- 实现两族枚举。
- 页面改用 `e8-root-explorer-v2`。
- 删除 payload 手工结果表。

### 里程碑 B：构建与前端

- 构建 finalized E8 Wasm。
- Worker runtime 加载 ready resources。
- 实现根族选择和坐标列表。

### 里程碑 C：几何视图

- Coxeter/坐标投影。
- selection 和 antipodal highlighting。
- density/radius 交互。

### 里程碑 D：形式证书

- size 定理。
- membership 和 norm soundness。
- 完备性证明。
- UI 链接正式 Lean 声明和证明页面。

## 验收标准

- 页面 JSON `execution.status = ready`。
- 前端不含 `112`、`128`、`240` 的执行逻辑硬编码。
- 浏览器调用 Lean/Wasm 返回 240 个精确根。
- 两族数量分别为 112、128。
- 每个根 8 维且 denominator 为 1 或 2。
- 每个根的精确范数平方为 2。
- UTF-8、错误输入、超时和 Worker 重建正常。
- 静态 PDF fallback 保留。
- 手机和桌面可用。
- 禁用 JavaScript 时论文正文仍完整。
- 页面明确区分计算枚举、二维可视化和一般性形式证明。
