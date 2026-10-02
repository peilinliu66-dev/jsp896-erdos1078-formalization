# JSP896 / Erdős 1078 独立数学及原题范围审计

审计日期：2026-10-02（Asia/Shanghai）。本报告审查原题、候选 Lean 声明及实际证明路线；**它本身不是编译、公理检查或内核重放结果**。编译由 `build896` 单独执行，应与其最终构建记录一起阅读。

**源代码审查结论：未发现致命数学错误、原题范围缩小或最终定理的未履行数学接口。可以继续实际编译及修复 API/演算错误。** 对完整奇数路线分别进行了结构路线与终结路线的独立只读复核，而非直接接受附件中的 `independent-r5-review.json`。成功提交仍以最终源码的实际构建和传递公理审计为准。

源码哈希、45 个根依赖模块的闭包及去除嵌套注释/字符串后的禁用词扫描见 `mathematical_scope_snapshot.json`；采集器是 `math_scope_collect.py`。当前 root `JSP896.lean` 的本地闭包覆盖全部 44 个 `JSP896/*.lean` 模块，另有根文件本身，共 45 个。附带两份 Lean 公理检查入口也纳入哈希记录。扫描未见 executable `sorry`、`admit`、`axiom`、`native_decide`、`unsafe`、`sorryAx`，这项扫描不代替实际公理依赖输出。

## 1. 原题、精确公式与量词

令 `r ≥ 2`、`n ≥ 1`、`s = floor(r/2)`，

\[
D(r,n)=\left\lceil\frac{sn}{2s-1}\right\rceil,
\qquad T(r,n)=(r-1)n-D(r,n).
\]

`Statement.lean` 中的顶点类型为实际 `Fin r × Fin n`；`IsPartite` 禁止类内边，`degree` 是过滤整个顶点集合得到的实际邻居数。`HasTransversalClique` 与 `HasIndependentTransversal` 都由实际函数 `Fin r → Fin n` 取每类一顶点，并检查全部不同类对。没有只检查类图、压缩模型或数值条件。

`FullResolution` 对全部 `r,n`、任意上述图量化：若每个顶点度数严格大于 `T`，得到实际横截团；对每个同样的 `r,n`，还构造所有度数至少 `T`、没有横截团的实际图。因类内无边，大小为 `r` 的团自然恰取每类一个顶点；这个表述与平衡 `r` 部图原问题相符。

`Main.lean` 的最终两个端点没有 certificate、cell partition、component model、switching theorem、source-paper theorem 或 `FullResolution` 作为额外参数。内部定理可带这些接口，但最终组装逐项构造、履行了它们。

`independentThreshold` 的自然数表达式确为正分母上的上取整：`s≥1`、`b=2s−1≥1`，因此 `(sn+b−1)/b` 不涉及自然减法截断风险。`ThresholdArithmetic.lean` 给出

\[
d<D(r,n)\iff(2s-1)d<sn,
\qquad 1\le D(r,n)\le n\le(r-1)n.
\]

没有整除、偶数 `n`、足够大的 `n` 或固定有限 `r` 的额外假设。`n=0` 不纳入原图定理；辅助取整定理允许 `n=0` 并不改变最终范围。

## 2. 补图与充分界的严格方向

`crossComplement` 仅在不同类间取补。`Complement.lean` 直接证明原图邻居与补图邻居不交，其并为所有跨类顶点，因此

\[
\deg_G(v)+\deg_H(v)=(r-1)n.
\]

结合 `D≤(r−1)n`，`deg_H<D` 与 `deg_G>T` 等价，`deg_H≤D` 与 `deg_G≥T` 等价。实际横截团与实际独立横截也直接互相转换。精确阈值的减法、严格性和等号例方向正确。

## 3. 小类数及偶数类数

`r=2`：`D=n`。任取第一类顶点，度数 `<n` 保证第二类存在非邻居，二者给出独立横截。正 `n` 保证第一顶点存在。

`r=3`：同样 `D=n`。在补图中所有度数 `>n`，按三类循环方向取 forward degree 最大的顶点 `v`，其 forward degree 记为 `M≤n`。其 backward neighborhood 非空，取其中 `w`。`w` 的 forward degree `≤M`，故其 backward neighborhood 与 `v` 的 forward neighborhood 总大小 `>n`；它们落在同一类，必相交。实际交点和 `v,w` 给出三类三角形。源码证明了邻居分解、基数、不交/交集条件及最终 transversal 函数，未调用未证三角形定理。

一般偶数 `r=2s`：有限最大独立部分横截和 feasible extensions 构造非空 domination certificate，若其活动类数为 `q`，则 `2≤q≤r`、证书顶点数 `≤2q−2`，支配计数得

\[
qn\le(2q-2)d.
\]

因为 `q/(2q−2)≥r/(2r−2)`，这与 `(2r−2)d<rn` 矛盾。该条件对偶数类数恰为 `(2s−1)d<sn`；不是仅使用统一的 `2d≤n` 较弱界。`EvenSufficiency.lean` 的计数参数由真实证书提供。

## 4. 奇数结构路线及原图/子图边界

`Main.independentTransversal_of_odd_bound` 假设 `r=2t+1`、`t≥2`、`(2t−1)d<tn`，反设原图无独立横截，然后选择实际 **edge-minimal 的无独立横截 spanning subgraph `H`**。部结构及最大度上界传给 `H`。

最终矛盾是从 `H` 的证明得到 `HasFull H` 并直接违反 `H` 无横截；源码未将子图的独立横截错误地转移到原图。`CriticalEdge` 对每条实际边删除此边，利用 edge-minimality 的实际独立横截构造带指定边的 feasible seed，继而扩张为全类 induced matching configuration。指定边包含性被证明，而非输入最终定理的假设。

在该严格界下，有限 feasible certificate 的活动类和星大小计数强迫其成为真实全类 IMC：`2r−2` 个端点、诱导完美匹配、faithful acyclic connected class graph。此后所有 cell/counting/exchange 定理使用这些实际字段。

关键统一预算是对全部 `r≥5`，

\[
(2r-4)d<(r-1)n\Longrightarrow(4r-5)d<2rn.
\]

其标量差为 `2r(2r−4)−(r−1)(4r−5)=r−5≥0`；`r=5` 的等号差仍保留输入严格性，故没有丢失端点。unique-neighbor cells `A_i` 成对，设 `δ_i=d−|A_i|`；实际 incidence count 推出

\[
\sum_i\delta_i\le(4r-4)d-2rn<d.
\]

辅助图删除类内及 opposite-cell 边。对其假设的无横截 certificate，faithful class edges 和 nonisolated 字段给出逐类 multiplicity bound

\[
t_i\le |S|-1-\mathbf1_{i^*\in S}.
\]

这个强的逐类界是 `CertificateMultiplicity` 与 `PairedCellTransversal` 的真实推导，未用仅有总顶点数 `2|S|−2` 替代。配对加权计数随后对总删除量 `≤d`、每 residual cell 非空的任意删除构造独立横截。

`CellDeletion` 使用实际有限 sigma 顶点类型、实际残余 graph、fibers、度数和删除预算，将这些横截通过逐坐标 matching replacement 变成新 IMC。`ExpandedCells` 先证明每顶点 complete to exactly one core cell，继而对相反扩张单元的两个非邻接顶点做一次 simultaneous asymmetric deletion，构造使它们成为 opposite unique-neighbor cells 的 replacement IMC，强迫它们相邻。因此扩张单元成为覆盖全图的实际分割，且相反单元间完全连接。

每扩张单元大小 `≤d`，由整个分割覆盖全部 `rn` 顶点得大小 `≥rn−(2r−3)d`。任意 IMC 的 multiply-dominated 顶点数 `≤(2r−2)d−rn`。统一预算给前者严格大于后者，故每个 IMC 在每扩张单元至多一个端点；因端点与单元数相等，实际恰一个。指定边包含性最终排除所有额外边，构造 literal `BipartiteModel.edge_iff`。这里没有引用未获得全文的 Jin 结果，也没有调用论文中仅 `r≥7` 的结构定理来覆盖 `r=5`。

独立结构审查的详细结论见 `STRUCTURE_SCOPE_AUDIT.md` 与其独立源码快照。

## 5. 奇数组件：centroid、switches 和终端支配块

`OddComponents.hasFull_of_odd_components` 是独立组件定理，内部从真实 class tree 构造 centroid，令每 nonroot branch 至多 `t` 类；并构造 black/white 匹配端点与有向 parent relation。此定理的组件接口在上一节已由 `Main` 履行。

辅助 arc `x→y` 由 `x` 类中实际存在 `index(v)=black(y)` 的顶点定义，parent arcs 是它的实例，所以 root 到所有类可达。`switchSet` 取指定组件 white sides 并保留其余组件 black endpoints，通过精确 `edge_iff` 证明独立。

closed/cycle switch 从实际有向循环构造覆盖各类的独立集合；avoiding-path switch 对白 distinguished neighbor 与避开指定类的 root path 构造同样集合。均由 `hasFull_of_independent_cover` 选择实际横截；不存在 switching existence 的额外假设。无横截时，这两种构造迫使辅助可达反对称及 white-index dominance。

有限 dominator order 和 strict future-cardinality rank 选择终端 root-dominator block `L`。源码证明两个所需闭包：从 `L` 出发的 arc 仍在 `L`；`L` 中顶点的 nonroot dominator 仍在 `L`。每 dominated class 的 parent path 也经过块根，因此 `1≤|L|≤t`。

所有 `L` 类的图顶点都由该块的 black/white endpoints 支配，但块根的 black endpoint 不会成为其 distinguished neighbor，否则形成 cycle switch。实际删除此 endpoint 后构造 `D`，满足 `|D|≤2|L|−1`。取 `u=|L|`，由 `u≤t` 和严格界可推出 `(2u−1)d<un`，而支配计数给 `un≤|D|d≤(2u−1)d`，矛盾。

独立终结路线审查见 `ODD_TERMINAL_SCOPE_AUDIT.md`。它对有限有向对象进行的挑战检查只作补充，不能代替无穷范围的数学论证或 Lean 构建。

## 6. 每个 `r,n` 的实际 sharpness graph

`SharpnessTools` 的 graph 用实际 component/Boolean-side 标签定义邻接；同一组件相反 sides 完全连接。`position` 注入证明每个 opposite side 大小至多 `d`，从而实际邻居基数 `≤d`。类内无边、finite-class 重编号、isolated-class padding 及 no-transversal obstruction 都有证明体。

取 `k=s`、`d=D`，则 `kn≤(2k−1)d`。`n≤d` 分支的源码使用一个实际 `K_{n,n}` 加孤立部，足以阻止全部横截；数学背景中使用 `k` 个 `K_{n,n}` 也有效，但不是当前源码的构造。

`d<n` 分支设 `i=2d−n`、`a=n−d`、`q=(d−1)/i`、`u=d−qi`。源码从精确界推出

\[
 i>0,\quad 1\le q<k,\quad 1\le u\le i,
 \quad d=a+i=qi+u,\quad n=d+a=d+(q-1)i+u.
\]

因此任意 residue 都被覆盖。`q` 的正余数写法等于 Construction 3.3 的 `ceil((d−i)/i)`，没有额外的可整除前提。

两条实际 chain 各有 `q+1` 个 `n` 顶点类；leftover 类的尾部按 `i` 大小 packets 分配，最后 partial packet 用 `u` 正确补齐。`component/side/position` 三标签全局注入，reflection 只在中央组件相交而落在相反 sides。假设有独立横截，从 leftover 类的所选 B-side 沿链归纳强迫中央 B-side，反射链强迫中央 A-side，故出现真实边。padding 到 `2k` 部并在奇数时添一个孤立部，restriction 保留无横截。补图给原 clique formulation 的每个 `r,n` 反例，包括 `n=1` 和全部 ceiling residues。

这里的图存在性不是引用为公理，也不依赖 sufficiency theorem。

## 7. 原始两层渐近范围

精确有限结论和反例合起来识别真正 extremal threshold；`ThresholdAsymptotics` 不单凭公式极限声称解决原图问题。`fullResolution_with_asymptotics` 显式要求 `hfull : FullResolution`，而 `Main` 实际传入无参数的 `full_resolution`，故这个中间 bridge 不是遗留假设接口。

取整 sandwich 给每固定 `r≥2` 的 `D/n` 位于 `s/(2s−1)` 与其加 `1/n` 之间；它和跨类补图恒等式给固定 `r` 的 `T/n` 极限。大 `r` 极限通过 `floor(r/2)→∞` 复合 `k/(2k−1)→1/2`，覆盖全部趋于无穷的自然类数。

**文案及显式原式建议：** BES 原文使用 `c_r−(r−2)→1/2`，当前源码导出 `(r−1)−c_r→1/2`。二者严格等价，因为

\[
c_r-(r-2)=1-[(r-1)-c_r],\qquad1-\tfrac12=\tfrac12.
\]

因此没有数学范围遗漏，但提交的数学说明或 literal audit entry 应显式展示该恒等式及连续减法步骤，让审阅者直接核对原式。无需改变既有精确有限定义。

## 8. 来源和审计边界

原始文献在线全文与本地保存 PDF 均已对照核查：[Bollobás–Erdős–Szemerédi](https://users.renyi.hu/~p_erdos/1975-19.pdf) 给原 balanced-clique 问题及两层渐近；[Szabó–Tardos](https://www.renyi.hu/~tardos/tibortransversal.pdf) Construction 3.3 与 Corollary 3.6 给偶数 exact threshold 及 sharpness；[Haxell–Szabó](https://page.mi.fu-berlin.de/szabo/PDF/oddtransversal.pdf) Theorem 1.1 给奇数精确值，Theorem 4.1 的组件充分定理覆盖所有奇数。候选工程把所用 combinatorial dependencies 本身写成证明体，而非 named-theorem axiom。

这次独立审查没有运行 Lean、修改候选工程或发布材料；仅写入本 `verification/` 的审计文件。附件历史 source-only、independent-review 或完整证明声称没有被直接当作已验证结果。后续最终门槛仍是：锁定最终源码和同版本依赖，完整构建自然成功；原图端点的 literal statement 检查；完整传递公理依赖检查；可复现的运行日志及其源码哈希。API/战术编译修复如改变数学定义、hypotheses 或 theorem statement，应重新审查这些变化。
