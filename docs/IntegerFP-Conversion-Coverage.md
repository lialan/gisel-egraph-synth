# Integer / FP conversion：覆盖与分析接口记录

本记录基于 gisel-egraph-synth main `6b30621e4a6687615323a8ded4abfe3a7cfd917d`，
LLVM 子模块 `37a1706d0eac1774701a0a44d9fb4fa542f56fde`。
区分 LLVM 已有能力、本项目接入缺口和值得新增的通用分析；不把“合法”当成“有收益”。

## 本次已补齐

| 能力 | 实现与边界 |
| --- | --- |
| 整数转 FP 精度条件 | `fitsfp` 同时检查有符号/无符号最大幅度、已知尾零、有效精度和最大有限指数。覆盖低 24 位 i32→f32、较大但对齐的整数；只有非负事实不能证明 `2^24+1` 精确。 |
| FP 分析事实 | 接入 LLVM `computeKnownFPClass`；增加有限整数值、有限数值上下界。提取、采样、具体证明、CEGIS 与运行时查询使用相同语义。事实不蕴含 noundef。 |
| FP→int 条件 | `fprange` 使用向内舍入的整数区间，避免把 f32 的 `2^31` 当成 INT32_MAX；可为 saturating→plain 转换推导充分条件。 |
| 通用发现 | 默认 auto grammar；可选有预算的类型扩展。替换仍由算子语义枚举，未添加固定转换 peephole 作为候选来源。 |
| Legalizer | 标量候选加入 capability 过滤；转换表区分 integer/FP 类型；运行时按当前函数检查新指令、常量和 splat。legalization 后只接受 Legal，之前允许有处理规则的 action。 |
| 类型构造 | 新中间 integer/IEEE f16/f32/f64 类型可创建，保留向量形状与 legacy/extended LLT；未由匹配绑定的宽度固定在已证明的 schedule。 |
| E-graph | 精度 guard 可读取导入的 KnownBits，不再只看整数类型总宽；改写后重新建立分析缓存。 |

注意 refinement 的方向：`sitofp(fptosi(x))→x` 的 source 在越界时可以是
poison，因此证明不一定需要范围条件；负零、非整数值仍需排除。
`fptosi_sat(x)→fptosi(x)` 则必须防止 replacement 新增 poison。
不能为所有转换链机械附加同一组条件。

## LLVM 当前已经有的判断

[GISelValueTracking.h](https://github.com/llvm/llvm-project/blob/37a1706d0eac1774701a0a44d9fb4fa542f56fde/llvm/include/llvm/CodeGen/GlobalISel/GISelValueTracking.h)
已经提供 KnownBits、known FP classes、非 NaN、非 logical-zero、DemandedElts
以及带 use flags 的 FP class 查询。
[实现中的 G_SITOFP/G_UITOFP](https://github.com/llvm/llvm-project/blob/37a1706d0eac1774701a0a44d9fb4fa542f56fde/llvm/lib/CodeGen/GlobalISel/GISelValueTracking.cpp#L2169)
已利用 KnownBits 推断符号、非零和部分有限性，也排除 NaN、subnormal、负零。
这些不是 LLVM 缺失项；本次主要补了本项目的事实传递和条件语法。

## 值得加入 ValueTracking 的判断

以下接口名仅为提案，范围明确指本次检查的 GISelValueTracking 公共接口，
不声称整个 LLVM 都不存在类似工具。

| 编号 / 优先级 | 判断及典型用途 | 当前状态与建议 | 验证要求 |
| --- | --- | --- | --- |
| VT-1 / P1 | 整数集合是否能在指定 FP semantics 中精确表示 | 本项目已有 `knownIntFitsFP`。可形成复用的 KnownBits + APFloat semantics 工具，再由 GISelValueTracking 包装。不能只比较 bitwidth 与 precision，也不能只判断不会 overflow。 | 有/无符号、`2^p±1`、尾零、最大有限值；APFloat 与 SMT 对照；每个 demanded lane 成立。 |
| VT-2 / P1 | FP 值是否必为有限整数 | 本项目有有界递归 transfer；GISelValueTracking 当前 class API 不表达“整数值”。建议独立返回 integral/unknown，并与 FPClass 组合。 | 常量、int→FP、round/floor/ceil/trunc、select、向量；NaN/Inf、负零、poison 单独处理。 |
| VT-3 / P1 | 保守 FP 数值上下界 | class mask 不能表达 `x≤32767`。本项目已有有限区间及部分 transfer；值得增加公开区间结果，随后覆盖 min/max/clamp、算术、PHI 的有界迭代。 | APFloat 定向舍入、overflow、NaN、denormal mode；循环终止及缓存失效；抽样必须处于事实区间。 |
| VT-4 / P1 | FP→int 是否保证不产生越界 poison | 当前 `fprange` 是闭整数区间的充分条件，尚不最精确。可增加针对 RTZ 的 safe-conversion 查询：unsigned 允许 `-1<x<2^N`，signed 允许 `-2^(N-1)-1<x<2^(N-1)`，均排除 NaN/Inf。 | fractional 边界（如 -0.5→unsigned）、nextafter、INT_MAX 向外舍入；plain 与 saturating 双向区别。 |
| VT-5 / P2 | select/分支条件对范围与 integral 的收紧 | LLVM 已有部分 select 的 FP class 过滤。本项目范围只合并两个分支的包络，尚未利用比较条件；本地递归 join 也可与已有更精细 class 结果相交。不要另造不兼容的路径分析。 | `select(fcmp x,C,...)`、有序/无序比较、NaN、共享输入；条件只在支配的使用点适用。 |
| VT-6 / P2 | FP narrowing 精确性及是否有双重舍入 | 尚未形成可查询事实；当前依赖候选 SMT 证明。可考虑“可精确表示于目标 semantics”的值事实，支持跨 FP 宽度转换及整数转换重排。 | midway、subnormal、ties-to-even、overflow、sNaN；不能由有限性或 integral 单独推出。 |
| VT-7 / P2 | 逐 lane 事实及 use-sensitive FP 环境 | 当前本地事实合并所有 fixed-vector lanes；支持 proof 的 all-lanes 条件，但未保留每 lane 区间。LLVM 已有 DemandedElts/flags 查询，值得接入相同接口。 | 未要求的 lane、shuffle、负零、poison；use flags 不得变成无条件全局事实。 |

## 值得加入或更完整接入 Legalizer 的判断

[LegalizerInfo](https://github.com/llvm/llvm-project/blob/37a1706d0eac1774701a0a44d9fb4fa542f56fde/llvm/include/llvm/CodeGen/GlobalISel/LegalizerInfo.h)
的 `getAction(LegalityQuery)` 已经回答类型对应的 action；本项目的主要缺失是
构造并使用正确查询，并非 LLVM 没有合法性 API。

| 编号 / 优先级 | 值得做的判断 | 归属、当前状态及后续 |
| --- | --- | --- |
| L-1 / 已补 | 精确的 result/operand 类型与 type-index 查询 | 本项目接入缺口；转换表现在保留 integer/FP 区分，运行时从实际 LLT 查询。相同位宽不是相同 FP semantics。 |
| L-2 / 已补 | 当前阶段能否新建该指令 | 本项目接入缺口；pre-legalizer 接受可处理 action，post-legalizer 只接受 Legal。保留原有指令与新建指令区别。 |
| L-3 / P1 | 当前函数的 subtarget/feature profile 与离线表是否一致 | runtime 已按当前 MF 查询。离线表仍为提取时的 target/CPU/features 快照；多函数不同 target-features 应分表或显式记为 unknown，避免误剪枝。 |
| L-4 / P1 | 一个 legalization action 是否存在可完成且无环的具体处理路径 | `Lower/Custom/Libcall/WidenScalar` 不保证整条路径已经在实际 pipeline 中验证。值得在发现后的验证层执行有预算的 legalize + machine verifier 探测，并缓存类型/子目标/阶段身份；不把一次 action 当成功编译证据。 |
| L-5 / P2 | 查询是否包含全部依赖项 | 当前转换仅需类型。扩展 memory/target intrinsics 时需 MemDesc、地址空间、immediate/属性及 provider contract；缺字段时应返回 unknown。当前 intrinsics 仍由 provider 合约负责，不宣称通用 intrinsic legality 已解决。 |
| L-6 / P2 | 新中间类型是否有完整构造与使用路径 | 当前有限 palette + runtime guards 已补 scalar/fixed-vector；bf16、其它 FP semantics、scalable vector 需要先补语义模型、证明与类型身份，不能按位宽推断。 |
| COST-1 / P1 | legalization 后是否更少指令、是否增加 fallback/寄存器压力 | 这是独立收益验证/成本分析问题，不应成为 Legalizer 的“合法”布尔判断。当前验证记录最终静态指令、失败与 fallback；无硬件性能结论。 |

推荐先推进 VT-1～VT-4 的共享查询与精确边界，再做 L-3/L-4 的验证缓存，
最后扩展路径敏感范围、其它 FP semantics 和更强成本模型。每项应由自动发现的
未覆盖实例或独立收益数据驱动，避免只为一个手写 rewrite 加特判。

## 验证记录

详见同目录的实施验证记录；远端完整日志、SMT 证明、冻结身份与逐文件结果位于
本次工作树的 `build/validation/`。该目录不提交大体积编译器和临时语料。
