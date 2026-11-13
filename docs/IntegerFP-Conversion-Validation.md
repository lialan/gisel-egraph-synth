# Integer / FP conversion 验证记录

基线：main `6b30621e4a6687615323a8ded4abfe3a7cfd917d`，使用仓库固定 LLVM
`37a1706d0eac1774701a0a44d9fb4fa542f56fde`。所有构建与测试均在 nod 执行。

- Python：完整执行 613 项，167 秒；最后留下的旧 profile 状态错误在重新测量并 pin 后，`all` 流程复测通过。生成文件一致性检查在候选构建恢复后单独通过。新的 9 项 facts / discovery / synthesis / emitter / real-extraction 测试通过。最终相关 68 项复测全部通过，`emit --check` 通过。使用现有 Python 3.10 环境，测试 runner 为仓库已有的 Python 3.11 `TestCase.enterContext` 调用补兼容方法。
- C++：169 项通过，包括 APFloat 精度对照、向内舍入的整数范围、前/后 Legalizer 和新类型构造。
- MIR lit：11/12 通过。`AMDGPU/egraph-combiner-vector.mir` 在精确 main 独立构建上出现相同三个检查失败（xor_self、类型打印）；记录为基线问题，本次未改写其断言掩盖问题。新增 KnownBits 转换 MIR 正反例通过。
- 已有规则：124 条重新证明；加入自动发现的 4 条后，知识库有 128 条 verified rules，证明文件一并保存。
- 默认目标 profile：对比精确 main，AMDGPU 14 个文件和 AArch64 24 个文件可比较，最终静态指令差均为 0，无逐文件回归、编译状态或 fallback 变化。AArch64 另有两个 SVE SAT 文件两侧均编译失败，未纳入可比较样本。

## 自动发现与编译验证

`eval_fp_conversions.py` 从真实提取的 MIR 搜索，未向发现器提供替换模板。
发现 signed/unsigned 的 int→FP→int 与 FP→int→FP 四条有条件规则。
重复运行还验证了“已进入知识库但未默认选中”的规则能够重新发现并验证。

冻结规则后，在不同掩码的程序上编译执行生成的 matcher/guard：

| 掩码 | 关闭候选的转换数 | 开启候选的转换数 |
| --- | ---: | ---: |
| 8191 | 10 | 2 |
| 16777215 | 10 | 2 |
| 2147483647 | 10 | 6 |

最后一行保留了不能由符号条件证明精确的整数 round-trip；FP round-trip
可以依据自身独立事实简化。以上只证明机制生效，不是独立收益数据。

## 独立收益结论

冻结后首次读取的 14 个 AMDGPU 转换文件，两侧使用相同 compiler、相同
native combines、默认规则 B 和 synth cleanup，只开关新增规则 Delta：

- 14/14 编译成功，编译状态及 fallback 集合均不变；一个文件包含两侧共有的 fallback。
- 新规则应用 0 次；最终静态指令差 0；更好/更差文件均为 0。
- 因而本次没有证明独立语料收益。4 条规则只加入知识库，未默认启用。
- 该结论仅限此有界转换语料；没有 GPU/CPU 硬件吞吐、延迟或运行时间结论。

[结构化结果](IntegerFP-Conversion-Validation.json) 保存逐文件输入 hash、
编译结果、指令数和冻结 compiler/rules 身份。完整日志及可重放输出在远端
`/home/nod/gisel-int-fp-20261112/build/validation/`。

后续值得补的分析判断、现有 LLVM 能力与未覆盖边界见
[覆盖与接口记录](IntegerFP-Conversion-Coverage.md)。
