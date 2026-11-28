# 化简库的变量

全局变量都在 `src/default.pipe` 里定义（《[命令行和 --passes](../cli.md)》 第 3 节），默认值也写在那里；下面各表的"默认"就是那里的值。Rust 代码读其中大部分，它读哪些名字、怎样用（开关、预算、时限、只决定缓存大小）列在 Rust 的一张表里（`rust_vars::INNER`、`FLAGS`、`LIMITS`、`UNREAD`、`SETTINGS`、`RUN`、`time_limit`），启动时按名字对上：表里的名字都要在源文件里有定义，否则启动就报错。`extra`、`printed`、`pre_*`（第 1 节）、`unclustered_relate_leaves`、`unclustered_rewrites`、`unified_rewrites`、`cand_bit_splits`、`polish_rewrites`、`polish_wins` 只有默认管线读。上限（`max_leaves` 最多 6 等）由 `default.pipe` 的 `check_limits` 检查（《[变量与作用域](../lang/variables.md)》 第 2 节），下表的"上限"就是那里写的值。

## 1. 开关

每个内部 pass 是一个开关变量，值为 0 时它被关掉：在一串步骤里返回输入，作为 alternative 时不给出形式。不赋值就是开着的（`none` 算开）。pass 的开关由 `src/builtins.pipe` 里 `extern` 的属性 `@switch` 定义（同名的开关）；`poly_masked`、`semi_*` 不是函数，是 `poly_mba`、`semi_linear` 里的步骤，它们的开关和其他全局变量一样在 `default.pipe` 里定义（`semi_bit_split = 1`），Rust 的变量表把它们标成开关，启动时检查都定义了。Rust 代码按开关名记统计（`pass/semi_shapes`）。全部开关：

`lowbits unshift tfunc_whole relate tfunc unify_operands recombine cut_products shifted_xor simplify_rebuilt cluster_regions simba small_blocks wide_blocks poly_mba poly_masked rebuild_values common_multiple related_leaves one_wide_term semi_linear drop_unused clustered peel peel_clustered semi_grouped semi_peel_grouped semi_shapes semi_pairs semi_peel_shapes semi_split semi_scaled semi_bit_split semi_short_consts`

`default.pipe` 关掉的是 `semi_peel_shapes`（定义成 `semi_peel_shapes = 0`），其余步骤的开关定义成 1。

**预处理各种重建的开关**：`pre_unified pre_no_wide pre_split_bits pre_halve_first pre_over_products pre_over_const_bitwise pre_over_shared_bitwise pre_halve_input pre_unclustered`，在 `default.pipe` 里定义成 1，只有默认 `prepass` 读：`(cand pre_unified unified p)` 在 `pre_unified` 为 0 时不造这种重建（《[化简库的内置函数](builtins.md)》 第 3 节）。`--passes` 的 `pre=`、`pre+=`、`pre-=` 是对它们赋值的简写（《[命令行和 --passes](../cli.md)》 第 2 节）。`first`、`no_wide_abstracted` 两种没有开关（写成 `(cand 1 ...)`）。

其他开关：

| 名字 | 默认 | 含义 |
|---|---|---|
| `cut` | 0（默认 `pipeline` 里设成 1） | 开着时，因时限跳过的步骤把整次运行记为截断 |
| `rerun_input` | 1 | 结果是 `mixed` 时带上原输入重跑第一轮 |
| `prove_minimal` | 1 | 尝试证明项最小 |
| `relate_parts` | 1 | `relate` 对叶子多于 `relate_leaves` 的区域也按部分处理；不带 `clustered` 的重建里设成 0 |

## 2. 运行

| 名字 | 默认 | 含义 |
|---|---|---|
| `restarts` | 来自 `-m` | 总轮数；默认 `pipeline` 写 `(fix (restarts - 1) later)`，因为第一轮单独写出。程序没给时它和 `iter_limit` 是 `none` |
| `iter_limit` | 来自 `-i` | 每轮 egglog 重复调度几次 |
| `keep` | 2 | 预处理保留几个重建；读出时至少是 1（`keep = 0` 读作 1） |
| `extra` | 2 | 预处理还在改变结果时，额外跑几轮 |
| `printed` | 2 | 从打印结果再跑几轮（0 不跑）；默认 `pipeline` 写 `(fix (printed - 1) later)` |
| `match_limit` | 64 | back-off 调度：一条规则每次运行最多匹配几次，超过就被禁用；下一轮 egglog 起生效 |
| `ban_length` | 3 | back-off 调度：被禁用的规则先停几次运行；下一轮 egglog 起生效 |
| `num_type` | 来自 `-n`（`none` 读作 `i64`） | 数值类型，值是类型名（《[管线语言](../lang/README.md)》 第 1.1 节） |
| `trace` | 来自 `--trace`（`none` 是关） | 把预处理的各个重建和每轮的大小写到 stderr |

## 3. 预算与时限

| 名字 | 默认 | 含义 |
|---|---|---|
| `rewrites` | `none` | 剩下的未缓存 `rewrite` 调用次数，用完后 `rewrite` 原样返回（《[变量与作用域](../lang/variables.md)》 第 1 节） |
| `bit_split_budget` | `none` | 剩下的 `bit_split` 拆分对数；每个 `cand` 设成 `cand_bit_splits`（默认管线读的限值，Rust 不读） |
| `time_limit` | `none` | 截止时刻，赋值时从此刻起计毫秒（《[变量与作用域](../lang/variables.md)》 第 3 节）。bench 用 `-t` 乘以它的 `--time-limit` 比例（默认 0.8）设置，比例为 0 时传 `none`；写在 `--passes` 里的在它之后，所以优先。`time_limit = 0` 是 0 毫秒，立即到期 |

## 4. 限值

| 名字 | 默认 | 含义 |
|---|---|---|
| `semi_leaves` | `max_leaves` | 半线性区域最多几个叶子才重建 |
| `relate_leaves` | `max_wide_leaves` | `relate` 只处理叶子不多于此的区域 |
| `unclustered_relate_leaves` | 10 | 不带 `clustered` 的重建里，`relate` 只处理这么多叶子以内的区域 |
| `unclustered_rewrites` | 256 | 不带 `clustered` 的重建最多调用 `rewrite` 的次数，超过就放弃 |
| `unclustered_after` | 1024 | 其他重建的 `rewrite` 次数不超过此值时，才尝试不带 `clustered` 的重建 |
| `unified_rewrites` | 128 | 统一操作数后重建的最多 `rewrite` 次数 |
| `related_rebuilds` | 8 | `related_leaves` 最多重建几种组合 |
| `related` | 4 | `relate` 每个区域最多试几个算术叶子 |
| `bit_splits` | 4 | `bit_split` 每个区域最多重建几种拆分 |
| `cand_bit_splits` | 8 | 每个 `cand` 最多几对 `P op Q` |
| `splits` | 4 | `split_bits` 对一个项最多试几个变量位 |
| `split_depth` | 2 | `split_bits` 最多嵌套几层 |
| `split_runs` | 16 | 一次 `split_bits` 最多几次重建 |
| `split_size` | 64 | `split_bits` 只处理不大于此的第一次重建 |
| `split_max_unknown_bits` | 2 | `split_bits`：乘积因子最多几个未知位才按位分情况 |
| `block_leaves` | 12 | `small_blocks` 最多处理几个叶子 |
| `block_combos` | 32768 | `small_blocks` 穷举的组合数上限，也是 `wide_blocks` 搜索的步数上限 |
| `block_max_block` | 3，上限 5 | `small_blocks`：一个块最多几个叶子；系数从至多这么多个 1 的点插值，每块试全部 `2^(2^k)` 个真值表 |
| `block_descent_rounds` | 4 | `small_blocks`：组合太多、不能穷举时，坐标下降最多几轮 |
| `block_spread_points` | 8 | `small_blocks`：完整检查前先查几个分散的点，多数区域早早被排除；不改变结果 |
| `cluster_depth` | 2 | `clustered` 最多嵌套几层 |
| `poly_builds` | 512 | `poly_mba` 穷举选择时最多构造几个乘积，之后每层只取第一种 |
| `poly_branch_monos` | 128 | 展开的单项式多于此时，从一开始就每层只取第一种 |
| `polish_rewrites` | 2000 | 一次 `polish` 最多几次未缓存的 `rewrite` |
| `polish_wins` | 8 | 默认 `polish`（和 `polish=a,b,...`）最多采用几次 `smaller` 的结果 |
| `tiny_size` | 3 | 不大于此的重建不再细找：函数 `tiny`，`opaque` 要求重建大于它 |
| `max_leaves` | 6，上限 6 | 线性区域最多几个叶子才按 {0,1}^n 上的值重建（真值表是 `u64`） |
| `max_wide_leaves` | 16，上限 64 | 宽区域最多几个叶子才整体求值（`drop_unused`、`relate`、`peel`；用到的叶子是 `u64` 掩码） |
| `lowbits_max_bits` | 18，上限 63 | `lowbits`：一个子项最多枚举几个叶子位 |
| `lowbits_max_context_bits` | 18，上限 63 | `lowbits`：在上下文里证明时最多枚举几个叶子位 |
| `lowbits_narrow_context_bits` | 12 | `lowbits`：多于这么多叶子位的证明还要用 `lowbits_wide_budget` |
| `lowbits_max_try` | 256 | `lowbits`：枚举或在上下文里证明的子项最大多大 |
| `lowbits_max_values` | 4 | `lowbits`：子项最多几个不同的值时，才试着在上下文里换成其中之一 |
| `lowbits_max_product_bits` | 4 | `lowbits`：没有变量移位时，只枚举值由叶子低这么多位决定的含乘积子项 |
| `lowbits_budget` | 67108864 | `lowbits`：一次调用所有枚举的求值步数 |
| `lowbits_wide_budget` | 8388608 | `lowbits`：多于 `lowbits_narrow_context_bits` 位的证明的求值步数 |
| `lowbits_max_low_rebuild` | 64 | `cut_products`：截断常数后重建的乘积因子最大多大 |
| `lowbits_refine_bits` | 2 | `lowbits`：`refine_low` 在已知位之外多枚举几位 |
| `lowbits_max_refine_bits` | 12，上限 63 | `lowbits`：`refine_low` 总共最多枚举几个叶子位 |
| `lowbits_refine_budget` | 4194304 | `lowbits`：`refine_low` 一次调用的求值步数 |
| `lowbits_max_factor_terms` | 4 | `over_products`：多于这么多项的因子不展开 |
| `poly_max_monos` | 4096 | `poly_mba`：乘出来的积最多几个单项式，超过就不展开 |
| `poly_monos_per_node` | 4 | `poly_mba`：展开的单项式多于项的节点数的这么多倍时不重建 |
| `poly_factor_tries` | 3 | `poly_mba`：重建整个多项式时试几个公因子（下层只试一个） |
| `poly_max_factor_monos` | 64 | `poly_mba`：最多几个单项式的多项式才分解因式，也是按约化形式再重建一次的上限 |
| `poly_max_factor_vars` | 12 | `poly_mba`：最多几个合取的多项式才分解因式 |
| `poly_max_pivots` | 4 | `poly_mba`：分解因式时最多试几个主元合取 |
| `poly_max_roots` | 16 | `poly_mba`：系数方程的根多于此时只留几个可能的根 |
| `poly_max_factor_steps` | 4096 | `poly_mba`：分解因式时最多试几种根的组合 |
| `poly_max_solutions` | 8 | `poly_mba`：一个主元最多给出几种分解 |
| `poly_max_shifted` | 4 | `poly_mba`：最多几种分解把因子加减常数、和线性余项并列 |
| `poly_max_shifted_monos` | 4 | `poly_mba`：加减常数的因子最多几个单项式 |
| `poly_shifted_rest_ratio` | 2 | `poly_mba`：加减常数的分解旁边，线性余项最多是 `poly_max_shifted_monos` 的几倍个单项式 |
| `poly_max_atoms` | 4 | `poly_mba`：按掩码展开时最多把位分成几组 |
| `poly_max_masked_monos` | 16 | `poly_mba`：按掩码展开最多几个单项式（或普通展开的 `poly_masked_monos_ratio` 倍） |
| `poly_masked_monos_ratio` | 2 | `poly_mba`：按掩码展开也可以有普通展开的这么多倍个单项式 |
| `poly_max_masked_size` | 20 | `poly_mba`：只有一个两边都带常数的乘积时，按掩码展开的项最大多大 |
| `common_multiple_min` | 4 | `common_multiple`：提出的 `c` 的绝对值至少多大 |
| `common_multiple_tries` | 2 | `common_multiple`：最多试几个 `c` |
| `overlap_max_values` | 4 | `overlapping_terms`：表里不同的非零值多于此时不搜索 |
| `overlap_max_choices` | 16 | `overlapping_terms`：一个点的值是几组系数之和时，最多试几种取法 |
| `overlap_max_terms` | 3，上限 63 | `overlapping_terms`：最多搜几个位运算项的和 |
| `decompose_max_vars` | 5 | 找最短位运算式时，最多几个变量的真值表才试 `g(A) op h(B)` 分解（`decompose`） |
| `decompose_min_free_size` | 10 | `decompose`：要胜过的大小至少这么大时，才把自由点两种取值都试 |
| `decompose_max_free_classes` | 4，上限 63 | `decompose`：一边最多枚举几类自由点 |
| `decompose_fill_max_vars` | 3 | `decompose`：一边最多几个变量才填自由点 |
| `decompose_xor_max_shared` | 2 | `decompose`：`^` 两边最多共用几个变量，才把它们的函数异或进两边 |
| `related_leaves_max_arith` | 4 | `related_leaves`：最多几个和区域其他叶子相关的算术叶子 |
| `relate_max_written_out` | 2 | `relate`：试过 `related` 个算术叶子后，再试几个区域里也展开写出的叶子 |
| `relate_max_free_product` | 20 | `relate`：不是位运算操作数的乘积叶子最大多大才试 |
| `relate_max_parts` | 8 | `relate`：按部分处理宽区域时最多试几个算术叶子 |
| `relate_wide_max_percent` | 90 | `relate`：宽区域里没有叶子或项消掉时，结果至多是区域大小的百分之几才保留 |
| `unify_operands_max_leaves` | 8，上限 63 | `unify_operands`：算术操作数最多几个叶子才按 {0,1}^n 上的值比较 |
| `memo_contexts` | 4 | `rewrite`、`simba_memo`、`relate` 的缓存每个键最多存几个结果，多了丢最早的（0 不缓存） |
| `join_constants_max_leaves` | 3 | `join_constants`：两个叶子组合起来和常数一起重建时，最多几个叶子 |
| `join_constants_max_sets` | 10 | `join_constants`：每个区域最多几次和常数一起的重建 |
| `join_linear_max_groups` | 12 | `join_linear`：区域最多几个叶子组才在组间移动叶子 |
| `join_linear_near_slack` | 4 | `join_linear`：一次移动最多多出几个节点，还能接着再移一次 |
| `join_linear_near_moves` | 3 | `join_linear`：最多几个这样的移动接着再移一次 |
| `join_linear_max_near_groups` | 8 | `join_linear`：区域最多几个叶子组才接着再移一次 |
| `shift_cases_depth` | 2 | `shift_cases`：最多嵌套按几个变量移位量分情况 |
| `shift_cases_max_size` | 64 | `shift_cases`：只处理不大于此的项（每个移位量最多重建 `2w` 种情况） |
| `shift_cases_amounts` | 2 | `shift_cases`：每层最多按几个移位量分情况 |
| `used_leaves_budget` | 33554432 | 宽区域在 {0,1}^n 上求值（`used_leaves`、`peel`）最多多少条指令乘点数 |
| `peel_min_size` | 16 | `peel`：区域的大小至少是叶子数的这么多倍才试 |
| `peel_spread_points` | 16 | `peel`：建位真值表之前，区域先要在几个分散的点上像位运算 |
| `wide_blocks_max_term_leaves` | 10，上限 63 | `wide_blocks`：一项最多几个叶子才展开 |
| `wide_blocks_max_block` | 10，上限 63 | `wide_blocks`：一个块最多几个叶子才重建成一项 |
| `wide_blocks_steps` | 4096 | `wide_blocks`：每个块、每个乘数找真值表的搜索步数 |
| `wide_blocks_max_tables` | 4096 | `wide_blocks`：不多于 6 个叶子的块最多收集几个真值表 |
| `wide_blocks_max_wide_tables` | 16 | `wide_blocks`：多于 6 个叶子的块最多收集几个真值表（按不相交分解写出，慢） |
| `wide_blocks_max_functions` | 64 | `wide_blocks`：每个块留几个最小的真值表给块间的搜索 |
| `wide_blocks_cache_size` | 4096 | `wide_blocks` 的线程级缓存最多存几个区域，满了清空 |
| `wide_blocks_descent_rounds` | 4 | `wide_blocks`：分支定界之前坐标下降最多几轮 |
| `wide_blocks_min_ratio` | 2 | `wide_blocks`：区域小于各块最小项大小之和的这么多倍时跳过（差不多已是块的形式） |
| `shapes_max_size` | 15，上限 15 | `semi_shapes`、`semi_pairs`：带自由常数的位运算式最大多大（第 15 层的表约 100 MB） |
| `pairs_max_groups` | 8 | `semi_pairs`：区域最多几个位组 |
| `pairs_budget` | 500000 | `semi_pairs`：一次调用最多检查几个式子 |
| `pairs_max_size` | 12 | `semi_pairs`：两个式子的大小之和最大多大 |
| `pairs_max_scales` | 12 | `semi_pairs`：最多试几个系数（从小的开始） |
| `pairs_max_carries` | 4096 | `semi_pairs`：进位 DP 每一位最多几个进位，超过就放弃 |
| `semi_split_max_combos` | 64 | `semi_split`：每个集合最多试几种其他集合常数的组合 |
| `semi_half_flips` | 2 | `semi_linear`：最多几个位组把 `-2^(r-1)` 也读成 `+2^(r-1)` |
| `semi_max_merges` | 16 | `semi_linear`：按高位合并位组时最多枚举几种 |
| `semi_max_code_groups` | 4 | `semi_linear`：最多几个位组用常数叶子编码（每种编码都试） |
| `tfunc_max_vars` | 3，上限 4 | `tfunc`：子项最多几个变量（或位运算原子）才查表（求值点是定长数组） |
| `tfunc_max_size` | 7 | `tfunc`：查找表里的式子最大多大 |
| `tfunc_points` | 24，上限 24 | `tfunc`：查表时在几个点上求值（值是定长数组） |
| `tfunc_max_try` | 256 | `tfunc`：最大试多大的子项（大的很少能换，证明也贵） |
| `tfunc_max_carries` | 64，上限 128 | T-函数证明（`tfunc`、`lowbits`）：最多几个进位（进位状态是 `u128`） |
| `tfunc_max_states` | 512 | T-函数证明：每一位最多几个可达的进位状态，超过就放弃 |
| `tfunc_max_factor` | 255 | T-函数证明：展开成加法器的常数乘数（或它的相反数）最大多大 |
| `minimal_points` | 64 | 最小性证明：在几个点上比较项和更小的项 |
| `minimal_lanes` | 16，上限 16 | 只含 `+ - * & \| ^ ~ neg` 的最小性证明：低位值向量有几个点（定长数组） |
| `minimal_budget` | 2097152 | 只含 `+ - * & \| ^ ~ neg` 的最小性证明：最多组合几对项 |
| `minimal_max_vars` | 3，上限 31 | 枚举的最小性证明：多于 `2k - 1` 个节点的项最多几个变量（变量集是 `u32`） |
| `minimal_max_size_4bit` | 7 | 只含 `+ - * & \| ^ ~ neg` 的最小性证明：在 4 位里证明的项最大多大 |
| `minimal_max_size_8bit` | 5 | 只含 `+ - * & \| ^ ~ neg` 的最小性证明：在 8 位里证明的项最大多大 |

`lowbits_budget`、`lowbits_wide_budget`、`lowbits_refine_budget` 是普通变量（每次 `lowbits` 调用从它们开始计数），不是《[变量与作用域](../lang/variables.md)》 第 1 节的预算。`poly_mba` 的变量在每次展开开始时读一次；`poly_factor_tries` 只用于整个多项式那一层，下层总是只试一个公因子。
`decompose_max_vars`、`decompose_min_free_size`、`decompose_max_free_classes`、`decompose_fill_max_vars`、`decompose_xor_max_shared` 决定最短位运算式的搜索；线程级的真值表缓存按这五个值分开存，所以不同作用域里的不同值各建一份表。`memo_contexts` 只决定缓存留多少结果，不改变结果，所以不记入缓存读过的变量。
`wide_blocks_cache_size` 和 `memo_contexts` 一样只决定缓存留多少，不记入读过的变量；`wide_blocks` 的缓存键里有全部限值的哈希。带自由常数的位运算式按大小逐层建表，进程内共用；表里的式子与 `shapes_max_size` 无关，只是最大那一层的式子不当操作数，不存它们的真值表列表，所以值小时少建几层，值大时补上那一层的列表再接着建。
`tfunc` 的查找表进程内共用，按位宽、变量数和 `tfunc_max_vars`、`tfunc_max_size`、`tfunc_points` 分开建，所以不同作用域里的不同值各建一份，正常运行只建默认那一份；没用到的求值点上变量都是 0，值和第 0 个点相同，不改变查表的结果。`tfunc_max_carries`、`tfunc_max_states`、`tfunc_max_factor` 也决定 `lowbits` 在上下文里的证明，每次 `lowbits` 调用读一次。
