# 圆周率处二次与三次整系数多项式值的统一下界

**2026 年 11 月 19 日 · Lean 4.35.0**  
[主文 PDF](paper/endpoints.pdf) · [LaTeX 源码](paper/endpoints.tex) · [Lean 四项声明与审计入口](formalization/OddPiPowers/OddPiPowers/PolynomialValues/PolynomialEndpointsAudit.lean) · [原始公理输出](formalization/OddPiPowers/logs/polyval-PolynomialEndpointsAudit-20261119-01.log) · [完整验收记录](formalization/OddPiPowers/logs/polynomial-values-acceptance-20261119.json)

给定非零整系数多项式 $P(X)=\sum_j a_j X^j$，定义高度 $H(P)=\max_j |a_j|$。对下表中每个次数上限 $d$，均存在一个常数 $c_d>0$，使每个满足 $\deg P\le d$ 的非零 $P\in\mathbb Z[X]$ 都有

$$
|P(\pi)|\ \ge\ c_d H(P)^{-w_d}.
$$

同一个 $c_d$ 适用于该次数范围内的全部高度，包括非零常数多项式、可约多项式及非本原多项式。$\omega_d(\pi)$ 指所有使 $0<|P(\pi)|<H(P)^{-t}$ 对无穷多个不同的合格 $P$ 成立的实数 $t$ 的上确界，取值于扩展实数。

| 次数上限 | 精确端点 $w_d$ | 逼近指数推论 |
|---|---|---|
| $d=2$ | $16161227/1000000=16.161227$ | $\omega_2(\pi)\le 16.161227$ |
| $d=3$ | $3426527/125000=27.412216$ | $\omega_3(\pi)\le 27.412216$ |

## Lean 验收范围

2026 年 11 月 19 日的最终审计逐项检查了下面四个公开声明的完整类型，并对每一项执行了 `#print axioms`。命名空间为 `PiPolynomialValues`。[四项签名](formalization/OddPiPowers/OddPiPowers/PolynomialValues/PolynomialEndpointsAudit.lean) · [定理实现](formalization/OddPiPowers/OddPiPowers/PolynomialValues/PolynomialEndpoints.lean)

| 声明 | 结论 |
|---|---|
| `pi_quadratic_endpoint` | 所有次数至多二的非零输入满足上述统一下界，$w=16161227/1000000$ |
| `pi_cubic_endpoint` | 所有次数至多三的非零输入满足上述统一下界，$w=3426527/125000$ |
| `pi_quadratic_omega_le` | $\omega_2(\pi)\le16161227/1000000$ |
| `pi_cubic_omega_le` | $\omega_3(\pi)\le3426527/125000$ |

四项的传递公理依赖完全相同，均只有 `propext`、`Classical.choice`、`Quot.sound`。因此这些结论的依赖链中没有 `sorryAx`、项目新增数学公理或原生求值公理。两个正数 $c_d$ 以存在量词给出。显式数值 $c_d$、指数最优性和一般次数的渐近界均在这次验收范围以外。[Lean 原始输出](formalization/OddPiPowers/logs/polyval-PolynomialEndpointsAudit-20261119-01.log)

| 计数口径 | 实际覆盖 |
|---|---|
| 四项定理的本地导入闭包 | 696 个本次多项式模块（695 个编译对象及 1 个最终审计入口），另导入此前已验收的 254 个本项目基础模块，共 950 个本地源码文件。外部依赖按清单固定版本。 |
| 本次多项式工作的全部成功记录 | 725 个源码入口，包括上述闭包和辅助检查。701 个入口生成了已归档的 `.olean`，24 个为只检查的入口。 |
| 随附的基础源码 | 此前 P1–P6 构建清单的完整 264 个源码文件，其中包含上述 254 个实际导入项。 |
| 实际参考见证 | 二次实例使用 104 个普通场、7 个带锚点场，三次实例使用 93 个普通场、4 个带锚点场，共 208 个。 |

验收使用 Lean `v4.35.0`，mathlib 提交 `56a005855ea17e0b0958f73ec801ae140b0a1679`。各证明作业串行运行，单线程、Lean 内存上限 2048 MiB、进程树上限 6144 MiB、每个入口时限 180 秒。最终导入闭包内的最高进程树峰值为 5600.86 MiB，四项合并审计为 4912.98 MiB。[依赖清单](formalization/OddPiPowers/lake-manifest.json) · [最终审计资源记录](formalization/OddPiPowers/logs/polyval-PolynomialEndpointsAudit-20261119-01.job.json)

## 复核与重放

**离线核对原始验收证据。** 在仓库根目录，使用 Python 3.11 或更高版本运行以下命令。它核对四项签名和原始传递公理输出，重算本地导入闭包，并核对逐模块的源码、日志、资源记录和 701 个归档编译对象的 SHA-256。该命令无需安装 Lean，重新编译的入口另列如下。

```shell
python -B scripts/check_release.py
```

[逐模块索引](evidence/serial-checks.json) · [701 个原始编译对象](evidence/accepted-polynomial-oleans.zip) · [725 组原始运行日志与资源记录](formalization/OddPiPowers/logs/)

**在 Lean 中重新编译。** 先用 `--plan` 从源码计算构建顺序。实际重放使用 Windows、Python 3.11+、Git、Elan 和已安装的 `leanprover/lean4:v4.35.0`。将依赖清单固定的九个 Git 检出及其对应版本的已构建依赖缓存放在 `formalization/OddPiPowers/.lake/packages/` 下，目录名与清单一致。已有同版本环境可以复用这整个 `packages` 目录。仓库提供项目源码与验收证据，外部数学库的缓存由重放环境提供。

```shell
python -B scripts/replay.py --plan
python -B scripts/replay.py --build
```

`--build` 依次编译最终闭包的 949 个前置源码入口，再执行最终四项审计。只重放最后一步时，先准备好与这份源码匹配的本地编译缓存，再运行 `python -B scripts/replay.py --audit-only`。两个编译选项都调用原有的受限运行器。启动前至少需要 2560 MiB 可用物理内存和 12288 MiB 可用系统提交量。重放日志写入独立的 `logs/replay/` 子目录。归档的 701 个对象供哈希查验，独立重建所需的全部导入来自源码和固定依赖。[内存限制运行器](scripts/bounded_lean.py) · [依赖版本检查](research/pi_low_degree_lean_prep_2026-11-19/check_module.py)

## 文稿

主文包含精确端点、从统一下界推出逼近指数的论证、数值见证概况和验收范围。LaTeX 源文件独立，使用含 Fandol、Libertinus 字体的 TeX Live 在 `paper/` 目录下运行两次 `xelatex endpoints.tex` 即可排版。[PDF](paper/endpoints.pdf) · [LaTeX](paper/endpoints.tex)

背景讲义保留旧版见证的 $16.1942$、$27.4188$，并讨论充分大次数的渐近系数 $8.32$。该渐近结论及讲义中的其他推广均未纳入上述四项 Lean 验收。[中文 PDF](paper/background/2026-11-19/polynomial-values-zh.pdf) · [中文 LaTeX](paper/background/2026-11-19/polynomial-values-zh.tex) · [English PDF](paper/background/2026-11-19/polynomial-values-en.pdf) · [English LaTeX](paper/background/2026-11-19/polynomial-values-en.tex)

**English summary.** For degree ceilings two and three, the formal development proves uniform lower bounds on the values of all nonzero integer polynomials at $\pi$ with exponents $16.161227$ and $27.412216$, respectively. The other two audited declarations bound the corresponding approximation exponents. The four transitive axiom reports list only `propext`, `Classical.choice`, and `Quot.sound`. The large-degree asymptotic in the background manuscripts lies outside this audit.
