# 两种冻结展开的良基性形式化

“把后续表达式才出现的弱展开提前到原表达式”这一设想由原 0-Y 展开器作者提出。本目录围绕这一设想，形式化内部侧枝版与坏根直连版共用的数值构造、可执行下降证书，以及通过证书后的展开终止性。

证明适用于全部合法 0-Y 表达式：空序列，或首项为 1、各项为正整数的有限序列；不要求输入是标准式。这里的结论是**所定义展开关系良基，持续采用认证步骤的迭代必到空式**。它不是全部合法表达式的字典序良序，也不是“完美无提升”定理。

## 两派的具体构造

行、列均从 0 编号。对表达式 $s$，记末列为 $x=|s|-1$，普通山脉展开位置 `expansionSite` 为 $(h,y)$：$h$ 是末列仍有父项的最高行，$y$ 是该行末列的父项，即坏根。记 $p_r(c)$ 为原山脉第 $r$ 行第 $c$ 列的父列，

$$
\operatorname{Anc}_{r-1}(x)
$$

为第 $r-1$ 行末列的严格祖先集合。冻结候选必须满足

$$
0<r<h,\qquad y<c<x,\qquad
c\notin\operatorname{Anc}_{r-1}(x),
$$

且 $p_r(c)$ 存在。两派只在最后一个条件上不同：

| 策略 | Lean 名称 | 对原父列的要求 |
| --- | --- | --- |
| 内部侧枝版（v0.4） | `FreezePolicy.internal` | $p_r(c)\ge y$ |
| 坏根直连版 | `FreezePolicy.directRoot` | $p_r(c)=y$ |

没有展开位置时，候选列表为空。`freezeCandidates` 按行、列递增枚举候选；`mem_freezeCandidates_iff` 证明枚举与上述判定一致。`FrozenValid` 要求冻结列表无重复，且所有位置均为该策略的候选。

`freezeExpand s F n` 是具体的数值算法：复制普通展开的最高活动行，再从上向下按复制父图逐层求和。被 $F$ 选中的原父边在复制块中保留原端点；其余父边使用普通展开的平移规则，块首列仍由原末列的父项确定。参数 $n=0$ 时直接删除末项。

[Construction.lean](ZeroY/NoLift/Construction.lean) 已证明：任意冻结列表都产生合法表达式；空冻结列表恰为普通 `expandY`；冻结不改变普通展开的输出长度；直连版的合法冻结集也是内部侧枝版的合法冻结集。**合法性不包含标准性，也不足以保证下降。**

## 实际检查的下降证书

[Certificate.lean](ZeroY/NoLift/Certificate.lean) 提供两种有限、可执行的检查。检查对象是构造出来的实际输出，不是调用者声明为正确的父图或下降结论。

1. **同列祖先证书。** 对候选输出 $t$ 与普通输出 $E(s,n)$ 重新编码。`sameColumnParentCheck` 检查列数相同，并要求候选编码中的每条直接父边，在普通输出编码的同一行、同一列上对应一条严格祖先路径。检查遍历所有可能存在父边的存储位置；范围外没有遗漏父边的结论也已证明。因此它覆盖完整规范父图，包含高于原展开行的部分。`sameColumnParentCheck_sound` 将布尔检查成功转换为 `AncestorEmbedding`。
2. **普通路径证书。** 证书给出一个非空参数列表。`runPath` 从原输入开始实际执行这些普通展开；`checkPath` 检查原输入非空，且所得终点与候选输出完全相同。`checkPath_sound` 证明成功意味着严格普通下降。这里验证给出的路径，不证明某种贪心寻路算法总能找到路径。

`checkDescent_sound` 将两类检查成功统一转换为已有关系 `MixedYStep`。该关系是 BMS 祖先弱化下降关系的非空传递闭包，再经 `encode` 拉回 0-Y 表达式。其良基性复用稳定表示的祖先嵌入拉回定理以及 BMS 展开的下降证明，允许普通路径与祖先证书交替使用。

## 两派的终止定理与选择接口

[WellFounded.lean](ZeroY/NoLift/WellFounded.lean) 中，一个 `Proposal` 只包含展开参数、冻结列表和下降证书。`checkProposal` 重新计算 `freezeExpand`，核验候选位置和下降证书；使用祖先证书时，还要求其普通展开参数与提案参数相同。

由成功提案定义的 `CertifiedStep policy` 已被证明包含于共同的 `MixedYStep`，从而两派均良基。`EitherStep` 还允许每一步改变策略；`certified_trajectory_terminates` 证明只要非空时继续采用认证步骤，轨迹最终到达空式。参数、冻结集和证书种类也可以逐步改变。

`chooseCertified` 从有限提案列表中选择，只保留通过检查的提案，并提供空冻结集的普通展开作为后备。调用者可以增加 `sourceFilter`，也可以自行指定 `prefer`；这些条件只影响从哪些认证结果中选择。`selected_trajectory_terminates` 进一步涵盖任意返回 `CheckedProposal` 的选择器。

直连版的**认证候选关系**包含于内部侧枝版的认证候选关系。不能由此断言，两派各自选取最优候选后得到的确定函数也存在同样的包含关系：缩小候选集可能改变最终选择。两派的终止性来自共同下降关系，不依赖这样的函数包含论断。

[Concrete/NoLiftConcrete.lean](Concrete/NoLiftConcrete.lean) 使用与原 0-Y 证明相同的已构造 BMS 下降模型，给出不再带模型参数的出口，包括：

- `internalStep_wellFounded`、`directRootStep_wellFounded`；
- `eitherStep_wellFounded`、`no_infinite_certified_chain`；
- `certified_trajectory_terminates`、`selected_trajectory_terminates`；
- `restrictedStep_wellFounded`，供进一步限制认证步骤使用。

## 尚未包含的结论

本次形式化没有把 HTML 程序的全部搜索过程证明为 Lean 程序的实现：候选子集枚举、两块来源筛选、贪心寻找来源路径、具体字典序最小选择及资源限额处理，仍需各自的实现对应证明。可执行证书检查的可靠性与整个 JavaScript 搜索的正确性是不同的结论。

尤其尚未形式化两块来源检查推出所有参数的恒等式

$$
C_F(s,n+1)=E(B_F,n).
$$

祖先证书也不自动证明来源表达式 $B_F$ 是 $s$ 的普通展开后代。普通路径分支只认证证书实际给出的路径。

此外，本次没有证明标准式闭包、原序数值保持、识别全部应提前的弱展开、全局无提升，或新规则后代集合的字典序良序。任意进一步来源筛选均可继承认证关系的良基性，但筛选自身具有何种数学含义，仍需单独论证。

## 复核入口

使用仓库固定的 Lean 4.33.1 及既有依赖配置，本次发布采用以下入口核验：

```text
# 在 formalization 目录
lake --wfail build ZeroY

# 在 formalization/Concrete 目录，使用 PowerShell
.\build-nolift.ps1
```

[Concrete/build-nolift.ps1](Concrete/build-nolift.ps1) 使用 Windows 本地依赖布局，执行 `lake --keep-toolchain --no-cache build NoLiftConcrete`，随后运行 `lake env lean NoLiftAudit.lean`。[NoLiftAudit.lean](Concrete/NoLiftAudit.lean) 明列审核对象；脚本只允许 `propext`、`Classical.choice`、`Quot.sound`。

2026-10-29 的发布核验中，主工程构建完成 70 个任务，具体模型增量构建（含依赖）完成 1573 个任务；19 项公理审核全部通过，各声明仅依赖上述三个标准公理的子集。
