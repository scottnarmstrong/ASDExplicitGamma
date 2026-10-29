# How the explicit proof differs from the proof in the paper

All numbers tagged **(notes)** below come from research notes and reviews that are not part of this repository, so a reader cannot check them from the repository alone. This note compares two proofs of the renormalization-group induction of

> S. Armstrong, A. Bou-Rabee, T. Kuusi, *Superdiffusion and anomalous regularization in self-similar random incompressible flows*, arXiv:2601.22142v2 (called "the paper" below).

The paper proves its induction for all sufficiently small $\gamma$, with a threshold that is not explicit. The proof formalized in this repository proves the induction for $\gamma \le \gamma_0 = 17/50000 = 0.00034$, for one concrete model. The purpose of this note is to show **what was changed** in the argument, so that one can judge **where the gain comes from**.

Numbering of the paper's results (Theorem A, B, C, Propositions 3.1, 3.4, ...) follows the compiled arXiv v2 text. The proof formalized here was written with AI assistance and then formalized in Lean; the notes behind it are called "the research notes of the explicit proof" and are not part of this repository. A number quoted below is marked **(Lean)** if it can be read off a Lean statement or certificate in this repository, and **(notes)** if it is reported by the research notes or by independent reviews of them and was not re-derived here.

## 1. Summary

**What the paper proves.** For every $\nu \gt 0$ and every $c_* \gt 0$ there is $\gamma_0(d,c_*) \gt 0$ such that for $\gamma \le \gamma_0$ the induction hypothesis $\mathcal S(m,E)$ of Definition 3.2 (a two-sided bound on $\bar\sigma_m^2$ and a two-term $\Gamma_2/\Gamma_{1/2}$ tail bound on the homogenization error $\mathcal E_{s,\infty,2}$) holds at every scale $3^m$ (Proposition 3.1). Theorems A, B, C are then derived. All constants are of the form "there exists $C(d)$"; the induction step requires $E \ge C c_*^{-1}$ and $\gamma \le E^{-10}$.

**What is proved here.** For the planar $q\otimes q$ Gaussian model with $\gamma \le 17/50000$, and for every $\nu \gt 0$ and every scale $m$: an explicit corridor for $\bar\sigma_m^2$, an explicit $L^p$ bound for $\mathcal E_s^2$ for all real $p \ge 1$, and an explicit two-term tail bound for $\mathcal E_s$. This implies the paper's induction hypothesis with $E = 2^{16}$. Everything is machine-checked in Lean, but only as an implication over models that satisfy the Gaussian-law hypothesis; the existence of such a model is not formalized (Section 2).

**What is not made explicit.** The sharp asymptotics (3.3) of $\bar\sigma_m$ in Proposition 3.1, the paper's regularity theorem (Theorem C), the homogenization theorem (Theorem B) and the quenched superdiffusivity theorem (Theorem A). The downstream steps of the paper still carry their own non-explicit constants.

**Where the gain comes from, ranked by importance** (a judgment based on the structure of the argument and on the margins reported in the notes; there is no controlled experiment that removes one change at a time, see Section 5):

1. **A different closing mechanism for the induction (new structure).** The paper's induction carries a free constant $E$ that is inflated by powers of $E$ at every step; the inflation is paid by the contraction of Proposition 3.23 (a factor $\varepsilon$ after $h\asymp\lvert\log\varepsilon\rvert$ scales), and the final absorption requires $E\ge c_*^{-1}\varepsilon^{-C}$ and $\gamma\le E^{-10}$ with $E$ large. The explicit proof carries instead a box of five numerical caps (plus an explicit corridor for $\bar\sigma$) that scale linearly with $\theta=\gamma/\gamma_0$ and closes it directly with numerical constants; the tail bounds are derived afterwards from the box and are not part of the induction.
2. **Specialization to a Gaussian planar model (model choice).** Gaussianity gives an exact heat-flow identity for adding a fresh shell, exact covariance constants of the $q$ kernel, sharp Gaussian concentration, and quarter-turn symmetry. These replace the generic sensitivity-plus-Orlicz estimates, whose constants are $C(d)$, by estimates with computable constants.
3. **A small number of sharpened inequalities** (a halved principal covariance coefficient, a pair of quarter-turn halvings, a vanishing-bracket lemma, a boundary-charge correction, and exact scalar continuity). The principal $\tfrac12$, the pair of halvings (not each halving alone), the vanishing bracket and the boundary charge are each needed at the threshold: without them a certified return fails at $\gamma_0$ (Section 5.2). Exact scalar continuity removes a loss but is not reported as decisive.
4. **Computer-checked certificates** (a 40-shell main-return comparison, a 129-lag recursion, 153 moment systems, and many exact rational gates). They do not create the gain; they make the thin margins (for instance $0.0592$ against $0.06$) checkable.
5. **Tracking of constants.** Necessary and laborious (it is most of the Lean code), but not by itself the source of the gain.

The sources report explicit ceilings on $\gamma$ for the Gaussian tail conditions: $3.576\cdot10^{-4}$ for the all-order step ($5.2\%$ above $\gamma_0$), the only ceiling that close to $\gamma_0$. Cruder concentration constants, at the notes' parameter choices, give ceilings below $\gamma_0$. Some relative margins at $\gamma_0$ are thinner than $5.2\%$ (main return, scalar upper error, strong-history cap), but the sources do not compute the largest $\gamma$ for which every step closes, so what determines $\gamma_0$ is not established (Section 5.2).

## 2. What is proved, and what is not

### 2.1 The two Lean theorems

Throughout, $B_m = \sum_{i \le m} h^2 3^{2\gamma i} = h^2\, 3^{2\gamma m}/(1-3^{-2\gamma})$ is the accumulated variance of the scalar stream; $\bar\sigma_m$ is the effective diffusivity of the paper (Lean: `Annealed.sigmaBar`); $\mathcal E_s=\mathcal E_{s,\infty,2}(\square_m;a_m,\bar\sigma_m)$ is the homogenization error of Definition 2.4 of the paper (Lean: `Observable.cutoffHomogenizationError`).

**Hypotheses (Lean `PlanarQ3Gaussian`).** Let $M$ be a model in dimension $2$ in the sense of the paper's standing assumptions (shell independence, exact triadic scaling, and (J1)–(J4), packaged in Lean as `ABKModel 2`), with $\gamma=M.\gamma \gt 0$ and $\nu=M.\nu \gt 0$. Let $h \gt 0$. Write the skew shell as $j_0=\psi J$, $J=\begin{pmatrix}0&-1\\1&0\end{pmatrix}$. The hypothesis is that for every finite family of points $x_i\in\mathbb R^2$ and reals $t_i$, the variable $\sum_i t_i\,\psi(x_i)$ is a centered Gaussian with variance

$$
h^2\sum_{i,i'} t_i t_{i'}\, c\big((x_i-x_{i'})_1\big)\, c\big((x_i-x_{i'})_2\big),
\qquad c(u)=\int q(y)q(y+u)\,dy,
$$

where $q(x)=\sqrt{3003/1024}\,(1-4x^2)^3\,\mathbf 1_{\lvert x\rvert\le 1/2}$ (so $\int q^2=1$). Lean: `PlanarQ3Gaussian`, `q3Kernel`, `q3Cov`.

**Theorem T1 (Lean `explicit_induction_bounds`).** Under these hypotheses, if $\gamma\le 17/50000$, then for every $m\in\mathbb Z$:

1. $\nu \le \bar\sigma_m$;
2. $\tfrac{31}{50}B_m+\tfrac{19}{50}\nu^2 \le \bar\sigma_m^2$;
3. $\bar\sigma_m^2 \le \nu^2+\tfrac{13}{8}B_m$;
4. (`AllOrderBounds`) for every $s\in[8\gamma,1]$:
   * (two-term tail) there are random variables $U,V$ with $\mathcal E_s\le \frac{2^{16}\sqrt\gamma}{s}\,U+\exp\!\big(-\tfrac{\log 2}{8192\,\gamma}\big)\,V$ in the sense of the paper's Lean library `Algsuperdiff`, `IsTwoTermBigOWith`, i.e. $\mathcal E_s \le O_{\Gamma_2}\big(2^{16}\sqrt\gamma/s\big)+O_{\Gamma_{1/2}}\big(e^{-\log 2/(8192\gamma)}\big)$ with the paper's Orlicz conventions (Appendix A of the paper);
   * (moments) for every real $p\ge 1$,
$$
\big\Vert \mathcal E_s^2\big\Vert_{L^p}\;\le\; \frac{2^{29}\,\gamma\,p}{s^2}+e^{-\log 2/(1500\,\gamma)}\,p^3 .
$$

The three constants $\tfrac{31}{50},\tfrac{19}{50},\tfrac{13}{8}$ are the corridor. The lower bound is a *mixed* bound; it does not give $\nu^2+0.62\,B_m$.

(The label T2 is not used in this note; the common higher-cutoff inverse bound that the research notes call T2 is not formalized, see Section 2.3.)

**Theorem T3 (Lean `inductionState_of_explicit`).** Under the same hypotheses and $\gamma\le17/50000$, for every $m_0\in\mathbb Z$ the paper's induction hypothesis $\mathcal S(m_0,E)$ of Definition 3.2 holds with $E=2^{16}$. In the Lean formalization of the paper this is the predicate `Algsuperdiff.Frozen.Section3.inductionState M m0 ⟨2^16,_⟩`. Concretely, for all $m\le m_0$,

$$
\tfrac14\max\!\big(c_*\gamma^{-1}3^{2\gamma m},\nu^2\big)\le\bar\sigma_m^2\le 4\max\!\big(c_*\gamma^{-1}3^{2\gamma m},\nu^2\big),
$$

and for $s\in[8\gamma,1]$, $\mathcal E_s\le O_{\Gamma_2}(2^{16}s^{-1}\sqrt\gamma)+O_{\Gamma_{1/2}}\big(s^{-2}\exp(-2^{-48}\gamma^{-1})\big)$. These are (3.4) and (3.5) of the paper with $E=2^{16}$; $c_*$ is the paper's disorder constant (for this model $c_*=h^2/(2\log 3)$, notes). The corridor of T1 implies the first display (lower: $\tfrac{31}{50}B+\tfrac{19}{50}\nu^2\ge 0.38\max(B,\nu^2)$; upper: $\nu^2+\tfrac{13}{8}B\le 4\max(\cdot)$ once one uses that $B_m$ and $c_*\gamma^{-1}3^{2\gamma m}$ differ by a factor at most $1.0012$, notes). The tail bounds of T1 imply the second display because $\log 2/8192\gt 2^{-48}$ and $s^{-2}\ge 1$.

**Verification status.** Both theorems are proved in Lean without `sorry`. The repository's records of an axiom check list exactly the standard axioms `propext`, `Classical.choice`, `Quot.sound` for the five main theorems (this was not re-run for this note). The numerical certificates are kernel-checked (`decide +kernel`); no `native_decide` and no custom axioms are used.

### 2.2 The intermediate theorems

T1 is assembled from three intermediate theorems about a state $P(n)$ (Lean `nativeInductionState`), stated for the same hypotheses:

* **entrance** (`molecular_entrance`): there is $K\in\mathbb Z$ (depending on $\gamma,\nu,h$) such that $P(n)$ holds for all $n\le K$;
* **step** (`induction_step`): if $P(n)$ holds for all $n\lt N$ then $P(N)$ holds;
* **all-order** (`allorder_of_state`): if $P(n)$ holds at every label then item 4 of T1 holds at every scale.

Strong induction on $\mathbb Z$ from the entrance gives $P(n)$ at every $n$. The state $P(n)$ consists of five *native* bounds, scaled by $\theta=\gamma/\gamma_0$ (Lean `theta`, `gammaZero`), and the corridor:

| quantity (at label $n$) | cap $\times\ \theta$ |
|---|---|
| ordinary mean $\mathbb E\,T(\square_n;a_n,\bar\sigma_n)$ (Lean `ordinaryMean`) | $\tfrac{3}{50}$ |
| strong history (`strong20`): $(1-3^{-1/4})\sum_{r\ge0}3^{-3r/20}\,\Vert T(\square_{n-r};a_n,\bar\sigma_n)\Vert_{L^{20}}$ | $\tfrac{2379}{2500}=0.9516$ |
| single-cube $L^{20}$ norm (`root20`) | $\tfrac{2013}{10000}=0.2013$ |
| buffered history (`buffer40History`): the same sum with cubes $\square_{n-40-r}$ | $\tfrac{61}{10}$ |
| buffered mean, cube 40 scales below (`bufferMean`) | $\tfrac{8}{25}$ |
| corridor | $\nu\le\bar\sigma_n$, $\tfrac{31}{50}B_n+\tfrac{19}{50}\nu^2\le\bar\sigma_n^2\le\nu^2+\tfrac{13}{8}B_n$ |

Here $T(U;a,\sigma)=\sigma^{-1}\mathrm{tr}A_{11}(U;a)+\sigma\mathrm{tr}A_{22}(U;a)-4\ge 0$ is the normalized trace defect of the coarse-grained $2d\times 2d$ matrix of the paper (Lean `traceDefect`, `cutoffTraceDefect`).

### 2.3 Scope: what the statements do and do not say

* **Existence of the model is not formalized.** T1 and T3 are implications: *if* a two-dimensional model with the standing assumptions (J1)–(J4) and the Gaussian shell law exists, *then* the conclusions hold. Constructing such a model (white noise convolved with the kernel, regularity, the tail condition (J2), the nondegeneracy (J4)) is not part of the Lean development. Note that (J2) is part of the model structure; the research notes record that for this Gaussian law (J2) holds only for sufficiently small amplitude $h$, which is harmless for the theorem because of amplitude invariance; the notes use $h=1/33000$, but the verification of (J2) at that value is not part of the Lean development. If no model existed, T1 would be vacuous. The threshold $\gamma_0$ itself does not depend on $h$ or $\nu$.
* **Dimension and kernel.** Only $d=2$ and the $q\otimes q$ Gaussian model are covered.
* **Only part of the paper's Proposition 3.1 is made explicit.** T1 gives the analogue of (3.2) (the two-term bound on $\mathcal E_s$, here with additional moment bounds) and of the corridor (3.4). It does **not** give the sharp asymptotics (3.3), $\lvert\bar\sigma_m-(\nu^2+c_*\gamma^{-1}3^{2\gamma m})^{1/2}\rvert\le Cc_*^{-2}\gamma^{1/2}\lvert\log\gamma\rvert\,\bar\sigma_m$, which needs the paper's Proposition 3.17 (an approximate recurrence for $\bar\sigma_m$) with explicit constants.
* **The paper's downstream results are not made explicit.** In the Lean library of the paper, the induction step is stated as $\exists C$, $E\ge C c_*^{-1}$, $\gamma\le E^{-10}$, $\mathcal S(m-1,E)\Rightarrow\mathcal S(m,E)$; the diffusivity asymptotics, the tail bounds, the regularity results of Section 4 and Theorems A, B, C are likewise stated with $\exists C$ and with smallness conditions of the type $\gamma\le C^{-10}c_*^{10}$. T3 produces a state at $E=2^{16}$ for $\gamma$ up to $3.4\cdot10^{-4}$, but the existing downstream statements need $\gamma\le E^{-10}=2^{-160}$ if applied to that state, so T3 does not by itself make them explicit. Making Theorems A, B, C explicit would need, in addition, a sharp scalar recurrence, coarse operator estimates, an explicit excess-decay iteration with random minimal scales, the process construction and exit-time estimates (the research notes list six such steps). None of this is done here.
* **The common higher-cutoff inverse bound is not formalized.** The research notes also claim a bound on $\sup_{N\ge\ell}\bar\sigma_\ell\,\lambda^{-1}_{\gamma,2}(\square_\ell;a_N)$ built on one probability space. It is not among the Lean statements; the notes' reviewers record that its $N$-uniform envelope had no written proof (notes).
* **Nothing is conditional inside the Lean theorems except through the stated hypotheses.** Every ingredient used in T1 and T3 is proved in Lean. The research notes contain claims that were not formalized (the common-cutoff inverse above, and several "valid but unadopted" variants, Section 4, item C18); they are labelled where they appear.

## 3. The paper's argument and where its constants are non-explicit

### 3.1 Structure of the paper's induction

The paper proves Proposition 3.1 by induction on the scale $m$ (Section 3). The state is $\mathcal S(m_0,E)$ (Definition 3.2): for $m\le m_0$,

* (3.4) $\tfrac14\max\{c_*\gamma^{-1}3^{2\gamma m},\nu^2\}\le\bar\sigma_m^2\le 4\max\{\cdots\}$;
* (3.5) $\mathcal E_{s,\infty,2}(\square_m;a_m,\bar\sigma_m)\le O_{\Gamma_2}(E s^{-1}\gamma^{1/2})+O_{\Gamma_{1/2}}(s^{-2}\exp(-E^{-3}\gamma^{-1}))$ for $s\in[8\gamma,1]$.

The step $\mathcal S(m-1,E)\Rightarrow\mathcal S(m,E)$ is proved under (3.6): $E\ge Cc_*^{-1}$ and $\gamma\le E^{-10}$, in four parts (Sections 3.3–3.6):

1. improved tail bounds for the coarse-grained ellipticity (Propositions 3.5, 3.6, with Proposition 3.10 and Lemmas 3.11, 3.12 and Proposition 3.15 on bad cubes, a Whitney partition and a piecewise affine approximation);
2. propagation of the diffusivity bounds (Proposition 3.17, from the approximate recurrence of Lemma 3.20 integrated in Lemma 3.21, and the continuity Lemma 3.22);
3. contraction of the coarse-graining defect (Proposition 3.23, via Lemma 3.24);
4. injection of the fresh shell and buckling (Proposition 3.27, Lemma 3.29, Proposition 3.28), which uses the coarse-grained sensitivity estimates of Section 2.4.

The base case is Proposition 3.4. The proof of Proposition 3.1 then fixes $E=Cc_*^{-1}$, so that the final condition is $\gamma\le C^{-10}c_*^{10}$. The all-order consequence (Theorem B) and the regularity theorem (Theorem C) are derived in Section 4 from $\mathcal S(m,E)$ at this $E$; Theorem A in Section 5.

### 3.2 Where smallness of $\gamma$ or a non-explicit constant is used

| Place in the paper | Role | Smallness / constants | How the paper handles it |
|---|---|---|---|
| Theorems A, B, C | statements | "there exist $\gamma_0(d,c_*)\gt0$ and $C(d,c_*)\lt\infty$"; Theorem A moments for $p\le C^{-1}\gamma^{-1}\lvert\log\gamma\rvert^{-6}$, Theorem B for $p\le C^{-1}\gamma^{-1}\lvert\log\gamma\rvert^{-1}$, Theorem C for $\alpha\le1-C\gamma^{1/2}$ | $\gamma_0$ is never computed; each section lowers $\gamma_0$ as needed (e.g. "after decreasing $\gamma_0$" in the proof of Theorem C) |
| Proposition 3.1 | induction output | $\gamma\le C(d)^{-10}c_*^{10}$; tail with $Cc_*^{-1}s^{-1}\gamma^{1/2}$ and $\exp(-C^{-1}c_*^3\gamma^{-1})$ | the constant $C(d)$ is the maximum of the constants of Propositions 3.17, 3.28 and of the choice $E=Cc_*^{-1}$ |
| Definition 3.2 and (3.6)–(3.7) | induction hypothesis and step | $E\ge Cc_*^{-1}$, $\gamma\le E^{-10}$ | $E$ is a free parameter fixed once at the end; every step loses a power of $E$ (below) |
| Proposition 3.4 (base case) | start at $m_{**}$, $\mathcal S(m_{**},C_{\rm start}c_*^{-1/2})$ | $C_0(d)$, $C_{\rm start}(d)$ | The proof is a short explicit computation ((3.41)–(3.43) and a cube-wise bound), with a dimensional $C_0$. This is the one place where the constants are essentially explicit already, up to $C_0(d)$ |
| Propositions 3.5, 3.6 (improved tails) | trimmed-sum argument: bad cubes at a mesoscopic scale are discarded | $\max(C,c_*^{-1})\le E\le\gamma^{-1/5}$ (3.44); (3.46) adds $E\ge\exp(C\sigma^{-1})$; output $C+O_{\Gamma_{1/2}}(\exp(-C^{-1}E^{-2}\gamma^{-1}))$ | deterministic constant $C(d)$ from Proposition 3.10, Lemmas 3.11–3.12 and Proposition 3.15, which use (J2) tails, a percolation estimate (Appendix B) and affine approximation; none is tracked |
| Proposition 3.17, Lemmas 3.20–3.22 | recurrence for $\bar\sigma_m$, its integration, continuity | $E\ge Cc_*^{-1}$, $\gamma\le E^{-10}$ (3.95); error terms $CE^2\lvert\log\gamma\rvert^2\gamma$ (3.107), output $Cc_*^{-1}E\gamma^{1/2}\lvert\log\gamma\rvert\,\bar\sigma_m$ (3.96); continuity (3.151) with defect $E^2\gamma\lvert\log\gamma\rvert$ | the proof notes that $\gamma\le E^{-10}$ gives $E^4\gamma^{1/2}\lvert\log\gamma\rvert\le16$ (in the proof of Lemma 3.22) |
| Proposition 3.23 (contraction) | after climbing $h\asymp\lvert\log\varepsilon\rvert$ scales the defect contracts to $\varepsilon E^2\gamma^{1/2}$ | $15c_*^{-1}\le E$, $\gamma\le E^{-10}$, $\gamma\le C^{-1}E^{-2}\varepsilon$ (3.153); output $O_{\Gamma_1}(\varepsilon E^2\gamma^{1/2})+O_{\Gamma_{1/4}}(\varepsilon\exp(-2E^{-3}\gamma^{-1}))$ | $C(d)$ from Lemma 3.24 (an $H^{-1}$ bound of the maximizer plus the subadditivity defect), Calderón–Zygmund and Poincaré constants of Section 2 |
| Propositions 3.27, 3.28, Lemma 3.29 (injection, buckling) | the fresh layers $j_{m-h+1},\dots,j_m$ are reinserted by coarse-grained sensitivity (Section 2.4: Lemmas 2.15–2.20) | $E\ge c_*^{-1}\varepsilon^{-C}$, $\gamma\le E^{-10}$ (3.177); output $O_{\Gamma_2}(CEs^{-1}(\varepsilon\gamma)^{1/2})+O_{\Gamma_{1/2}}(C\varepsilon s^{-2}e^{-E^{-3}\gamma^{-1}})$ | to close $\mathcal S(m,E)$ one needs $C\varepsilon^{1/2}\le1$, i.e. $\varepsilon=(2C_{(3.178)})^{-2}$; hence $E\ge c_*^{-1}\varepsilon^{-C}$ is forced |
| Proof of Proposition 3.1 | assembly | $E=Cc_*^{-1}$, $\gamma\le E^{-10}=C^{-10}c_*^{10}$ | one choice of $E$, then (3.3) from Proposition 3.17 |
| Section 4 (Proposition 4.8, Lemmas 4.4, 4.9, 4.14, Theorems C and B) | regularity and the all-order consequence | $\gamma\le C^{-10}c_*^{10}$ and further conditions such as $\gamma\le C^{-10}\min\{c_*^{10},\ \delta^2c_*^2 s^9\}$ (Proposition 4.8, as in its Lean statement; Lemma 4.9 has only $\gamma\le C^{-10}c_*^{10}$) | they consume $\mathcal S(m,E)$ at $E=Cc_*^{-1}$ and lower $\gamma_0$ again |
| Section 5 (Theorem A) | process | smallness of $\gamma$ at each exit-time and displacement estimate | not tracked |

The structural reason for $\gamma\le E^{-10}$ is visible in the table: the hypothesis carries a free constant $E$ in front of $\gamma^{1/2}$; each step returns the conclusion with a loss in $E$ (a factor $E$ in (3.178), $E^2$ in (3.154) and in the recurrence error, an $E^4$ in the continuity step), and these losses are paid by the $\varepsilon$-contraction of Proposition 3.23, with $\varepsilon$ fixed in the closing step (Proposition 3.28) as $(2C_{(3.178)})^{-2}$; the size $\gamma^{1/2}$ is that of the fresh-layer injection. The final absorption then needs $E\ge c_*^{-1}\varepsilon^{-C}$ and $\gamma\le E^{-10}$. In addition $E$ itself is bounded below by non-explicit quantities ($Cc_*^{-1}$, $\exp(C\sigma^{-1})$, $\varepsilon^{-C}$).

The constants $C(d)$ enter through at least the following inputs: Calderón–Zygmund and Poincaré constants of Section 2; the sensitivity estimates of Section 2.4; the Whitney and percolation arguments (Section 3.3 and Appendix B); the Orlicz algebra of Appendix A; and the concentration inequality of Appendix D.

### 3.3 What an honest explicit version of the paper's own argument would require

Tracking constants in the paper's argument, step by step, would require at minimum:

1. numerical values of every $C(d)$ listed above (for $d=2$);
2. a numerical value of the constant $C_{(3.178)}$ of Proposition 3.28, hence of $\varepsilon$ and of $E\ge c_*^{-1}\varepsilon^{-C}$ together with the exponent $C$;
3. then $\gamma_0\le E^{-10}$ and $\gamma_0\le C^{-10}c_*^{10}$.

The paper does not compute these, and the research notes do not attempt a numerical tracking of the paper's own constants. Hence **no estimate of the resulting $\gamma_0$ is supported by the sources**. The following are illustrations that are not from the sources:

* *(illustration, not from the sources)* If $E$ were as small as $2^{16}$ (the value that appears in T3), the condition $\gamma\le E^{-10}$ alone would give $\gamma\le2^{-160}\approx7\cdot10^{-49}$.
* *(illustration, not from the sources)* The condition $\gamma\le C^{-10}c_*^{10}$ depends on the disorder constant. For the normalization of the concrete model in the notes ($h=1/33000$, $c_*=h^2/(2\log3)\approx4.2\cdot10^{-10}$) one has $c_*^{10}\approx10^{-94}$, before dividing by $C^{10}$.

The explicit proof does not compete with these numbers by tracking the same steps; it changes the architecture so that neither $E$ nor $c_*$ appears (Section 4, items C1 and C16).

### 3.4 Correspondence of the steps

| step of the paper's induction | what it delivers | counterpart in the explicit proof | what the counterpart delivers |
|---|---|---|---|
| improved tails for $\lambda^{-1}$ (Propositions 3.5, 3.6) | $\lambda^{-1}\bar\sigma\le C+$ rare term | inverse bank (C8) | $\lVert B^*\rVert_{L^{128}}\le\beta=1.4103$, positive split with remainder $10^{-24}$ |
| diffusivity recurrence (Proposition 3.17, Lemmas 3.20–3.22) | (3.3) and (3.4) | scalar corridor (C3, C4, C5) | corridor $\tfrac{31}{50},\tfrac{19}{50},\tfrac{13}{8}$ and exact continuity; **no** analogue of (3.3) |
| contraction (Proposition 3.23) | defect after $h\asymp\lvert\log\varepsilon\rvert$ scales is $\le\varepsilon E^2\gamma^{1/2}$ | cold observation (C7) | mean defect $D_{40}=0.0343$ (at $\theta=1$) after $40$ scales |
| injection of fresh shells (Propositions 3.27, 3.28; Section 2.4) | tails of $\mathcal E_s$ at scale $m$ with constant $CE\varepsilon^{1/2}$ | main return (C11) and native heat step (C9) | mean defect $\le0.0592$ after $40$ insertions; $L^{20}$ caps of the native box |
| conversion to tails | built into the induction ((3.5)) | all-order step (C13) | $L^p$ bound for every real $p$, then the two-term tail |
| base case (Proposition 3.4) | $\mathcal S(m_{**},Cc_*^{-1/2})$ | entrance (C2) | $P(n)$ for $n\le K(\gamma,\nu,h)$ |

The first four rows correspond closely, step by step, to the structure of the paper's Section 3; the substance of the differences is in *how* each step is carried out (generic deterministic estimates with $C(d)$ versus a Gaussian heat-flow calculation with numerical constants) and in *what is carried through the induction* (the free constant $E$ versus numerical caps).

## 4. What changed, component by component

Classification used throughout:

* (a) same argument with constants tracked;
* (b) sharpened inequality (new lemma);
* (c) new argument or new structure;
* (d) computer-checked numerical certificate replacing an estimate;
* (e) specialization of the model ($d=2$, the concrete kernel, Gaussianity).

### 4.1 Overview table

| # | Component | Paper | Explicit proof | Class | Load-bearing for the size of $\gamma_0$? |
|---|---|---|---|---|---|
| C1 | Induction state and closing mechanism | $\mathcal S(m,E)$ with free $E$; loss in $E$ at each step | box of five native caps scaling with $\theta=\gamma/\gamma_0$, plus an explicit corridor; no free constant | (c) | Yes, structurally: removes $\gamma\le E^{-10}$ |
| C2 | Entrance (base case) | Proposition 3.4, start at $m_{**}$ | start deep in the molecular regime $B_n/\nu^2\le\theta/400$ | (a), (e) | No |
| C3 | Scalar corridor, lower | Proposition 3.17 via recurrence | variational trial with ten explicit error terms; reciprocal conversion; mixed bound $\tfrac{31}{50}B+\tfrac{19}{50}\nu^2$ | (c), (d) | Yes (margin $0.0020$) |
| C4 | Scalar corridor, upper | Proposition 3.17 | long-block trial $\sigma_{\rm new}\le\sigma_{\rm old}(1+z+e)$, concave barrier, ceiling $e=0.0681$ | (c), (d) | Yes (error $0.06804$ against ceiling $0.0681$) |
| C5 | Exact scalar continuity | Lemma 3.22 (approximate, with $E^2\gamma\lvert\log\gamma\rvert$) | exact: $1\le\bar\sigma_{m+h}/\bar\sigma_m\le3^{2\gamma h}$ | (b) | No (removes a loss) |
| C6 | Deterministic sensitivity and projection constants | Section 2.4, constants $C(d)$ | explicit constants ($D_f\lt1.260$, $f_D$, $c_D$, $E_\delta\lt1.309$, ...) | (a), (b) | Yes, through every error term |
| C7 | Cold observation (contraction) | Proposition 3.23, Lemma 3.24 | 129-lag triangular recurrence with an explicit plateau inequality; $D_{40}=0.0343$, $D_{128}=0.00475$ | (a), (b), (d), (e) | Yes: initial value of the main return |
| C8 | Inverse bank (trimmed averages) | Propositions 3.5, 3.6, 3.10, 3.15 | explicit reset, planar clusters and Whitney tiles; $L^{128}$ bound $\beta=1.4103$ with positive remainder $10^{-24}$ | (a), (e), (d) | Yes, through the Gaussian tail condition |
| C9 | Gaussian heat calculus and native moment systems | none (the paper uses sensitivity and Orlicz algebra) | exact heat identity for adding a shell; $L^{20}$ moment hierarchy with 153 positive moment systems | (c), (e), (d) | Yes: yields the native caps $0.95$, $0.20$, $5.9$, $0.32$ |
| C10 | Vanishing bracket | none | pathwise bound on the carré-du-champ of the trace defect, $\Gamma(T)\le4\kappa^2B^2TF$ | (b) | Yes: without it the $L^{20}$ returns are about $1$ rather than $0.2$ |
| C11 | Main return | Lemma 3.29 and Proposition 3.28 (injection) | differential inequality along $a_t=a_m+\sqrt t\,j_{m+1}$, 40 shells, affine panel comparison; return $0.0592\lt0.06$ | (c), (b), (d), (e) | Yes (margin 1.3 percent) |
| C12 | All $\gamma\le\gamma_0$ from the endpoint | single condition $\gamma\le E^{-10}$, monotone | $\theta$-proportional comparison $E_\theta(\theta f)\le\theta E_1(f)$ | (c) | No (needed because certificates are only computed at $\gamma_0$) |
| C13 | All-order consequence | Orlicz bookkeeping inside the induction; Theorem B for $p\le C^{-1}\gamma^{-1}\lvert\log\gamma\rvert^{-1}$ | derived afterwards from the state; all real $p$; $2^{29}$ and $2^{16}$ | (a), (b) | Yes, through its Gaussian tail condition (ceiling $3.576\cdot10^{-4}$) |
| C14 | Gaussian tail condition | (J2) tails, $C(d)$ | sharp sub-Gaussian exponent with Cameron–Martin Lipschitz constants | (e), (b) | Yes; the only step with a reported $\gamma$-ceiling close to $\gamma_0$ (5.2 percent above) |
| C15 | Numerical certificates | none | exact rational and interval certificates in Lean | (d) | No (they verify) |
| C16 | Choice of model | general (J1)–(J4), any $d\ge2$ | $d=2$, $q^{\otimes2}$ kernel, Gaussian | (e) | Yes, structurally |
| C17 | Bridge to the paper's state (T3) | — | $E=2^{16}$ | (a) | No |
| C18 | Items of the research notes not used | — | not formalized, not used | — | No |

### 4.2 Notes on each component

**C1. Induction state and closing mechanism (class (c)).**
*Paper.* The hypothesis $\mathcal S(m,E)$ contains the Orlicz tails (3.5) of $\mathcal E_s$ itself, with the free constant $E$; the step returns tails with a constant $C E$ and an $\varepsilon$ chosen to close (Proposition 3.28).
*Explicit proof.* The state is the box of Section 2.2: five numerical caps on moments of the trace defect, plus the corridor. All caps are *proportional* to $\theta$; they are closed in a joint step using the earlier labels only, without any premise at the label being proved. There is no parameter $E$. The Orlicz tails for $\mathcal E_s$ are then *derived* from the box (C13) and are not part of the induction.
*Why this matters.* It removes the loop "$E$ in, $CE$ out" and with it the condition $\gamma\le E^{-10}$ and the lower bound $E\ge Cc_*^{-1}$. The price is that the box has to close with explicit numerical margins, which is why the proof needs C6–C11 and the certificates.

**C2. Entrance (class (a), (e)).**
*Paper.* Proposition 3.4 proves $\mathcal S(m_{**},C_{\rm start}c_*^{-1/2})$ at the scale $m_{**}$, defined in (3.8) by comparing $\nu^2$ with a large negative power of $\gamma$ times the accumulated variance (and $m_*$ in (3.9) similarly with a smaller power), using $\nu\,\mathrm{Id}\le\bar\sigma_m\le\nu(1+\tfrac1{2\nu^2}c_*^+\gamma^{-1}(1+4\gamma)3^{2\gamma m})$ and a cube-wise bound for the defect.
*Explicit proof.* Entrance at every label with $B_n/\nu^2\le\theta/400$ (Lean `molecular_entrance`; $K$ depends on $\gamma,\nu,h$). There the skew part is negligible compared with $\nu$: $\nu\le\bar\sigma_n\le\nu+B_n/(2\nu)$ by a constant competitor and the projected molecular upper bound, the five native quantities are bounded by direct moment computations for Gaussian fields, and the corridor holds because $B_n\ll\nu^2$.
*Classification.* Same idea as the paper (the antisymmetric part has little effect on small scales), with a different starting condition and tracked constants. Not binding for $\gamma_0$.

**C3. Scalar corridor, lower bound (class (c), (d)).**
*Paper.* A linearization around $\bar\sigma_{m-h}$ gives the approximate recurrence of Lemma 3.20; Lemma 3.21 integrates it, with errors $CE^2\lvert\log\gamma\rvert^2\gamma$.
*Explicit proof.* A variational trial of the old Hessian at the completed label, with ten separately bounded positive error terms (the mixed source square, covariance terms, derivative feedbacks, a finite-parent error, ...), a quartic remainder controlled with the new resolvent, then conversion from the one-shell differential to a reciprocal inequality by a two-region argument. The intercept is mixed: $\bar\sigma_N^2\ge\tfrac{31}{50}B_N+\tfrac{19}{50}\nu^2$ (the notes use $0.62/0.38$). The favorable gain is $K=0.3143$ against the required $0.3123$ (notes), a margin of about $0.002$.
*Not in the paper.* The lower bound is *not* the sharp asymptotics (3.3) but a corridor; this is what is needed for the induction.

**C4. Scalar corridor, upper bound (class (c), (d)).**
A long-block trial (block length $\lfloor0.34/\gamma\rfloor$, source of depth $14$) gives $\sigma_{\rm new}\le\sigma_{\rm old}(1+z+e)$; the concave barrier $P(z)=2(U-1)z-z^2-2e(1+z)-e^2$ with $U=\tfrac{13}{8}$ is positive on the signal interval $[0.148,0.90]$ for $e=0.0681$. The complete error is $0.068039$ (notes), against the accepted ceiling $0.0681$; the originally intended ceiling $0.068$ fails. The molecular bound $\sigma^2\le\nu^2+\tfrac54B$ for $B\le\nu^2$ initializes every residue class. A planar boundary-cutoff lemma for the trial replaced a four-dimensional lemma whose proof diverges logarithmically in $d=2$ (notes).

**C5. Exact scalar continuity (class (b)).**
*Paper.* Lemma 3.22: $\bar\sigma_m\ge\bar\sigma_n/4$ and $\lvert\bar\sigma_m/\bar\sigma_n-1+\bar\sigma_n/\bar\sigma_m-1\rvert\le C\min\{1,\gamma(m-n)+E^2\gamma\lvert\log\gamma\rvert\}3^{2\gamma(m-n)}$.
*Explicit proof.* For the true $\bar\sigma$ and integers $m,h\ge0$: $1\le\bar\sigma_{m+h}(\nu)/\bar\sigma_m(\nu)\le3^{2\gamma h}$. The proof combines exact self-similar scaling $\bar\sigma_m(\nu)=3^{\gamma m}\bar\sigma_0(\nu3^{-\gamma m})$ with a spectral formula for the Dirichlet response, from which $D(\nu)/\nu$ decreases and $\nu D(\nu)$ increases in $\nu$. One identification step in the notes' first version (that the limit of the expected Dirichlet energy equals $\bar\sigma$) was unproved; the reviewers replaced it by a per-sample variational argument plus Jensen (notes). The statement is exact and carries no $E$. Not binding.

**C6. Sensitivity and projection constants (class (a), (b)).**
The paper's sensitivity estimates (Section 2.4) have constants $C(d)$. The explicit proof recomputes them for $d=2$ on triadic cubes: the Poincaré constants ($f_D=\sqrt{7/2}/\pi$, $c_1^2=(\sqrt3-1)/(\pi^2(1-\sqrt3/9))$, $c_D^2=c_1^2+1/(2\pi^2)$), paired coercivity, the forced-source constant $D_f=\tfrac12+3^{-1/4}\lt1.260$, an interpolation triple, and planar constants such as $E_\delta=1.30844\lt1.309$. These were re-derived by independent reviewers (notes). Two are genuinely new sharpened statements: the *paired* Bessel estimate (no factor 2 lost) and the half-coefficient in C11. Load-bearing: every term of the main return uses them (for instance the two oscillation constants $o_p,o_m$ have about $32$ percent of room jointly, notes; separately, the proved bounds use $c_0=0.43951$ against $0.440$ and $1/\pi$ against $0.319$ with little slack).

**C7. Cold observation (class (a), (b), (d), (e)).**
*Paper.* Proposition 3.23 contracts the defect of a coefficient $a_{l-h}$ observed on cubes $h\asymp\lvert\log\varepsilon\rvert$ scales above, via an $H^{-1}$ bound of the maximizer plus the subadditivity defect (Lemma 3.24).
*Explicit proof.* Fix a completed coefficient $a_n$ and its frame $\bar\sigma_n$. Let $D_k$ bound $\mathbb E\,T(\square_{n+k};a_n,\bar\sigma_n)$. A triangular recurrence over $129$ lags, using earlier means and histories only, with an explicit two-scale plateau inequality (constants $w_2=53/72$, $w_{2k}=28\cdot9^{-k}$, $C_T=4/[7(1-c)]$, $C_D=96/(49c)-1$), a graph lemma $\lVert A-I\rVert\le e+\sqrt{a^2/2+2e^2}$, and four-colour independence from the compact support of $q$. Results (notes): $D_{40}=0.034265$, $D_{128}=0.004746$. The original proof note of the plateau inequality was missing from the notes; it was reconstructed and found to reproduce the constants (notes).
*Role.* $D_{40}$ is the initial value of the main return (C11). For $\theta\le1$ the recursion is shown to satisfy $D_j(\theta)\le\theta D_j(1)$ at all $129$ lags.

**C8. Inverse bank (class (a), (e), (d)).**
*Paper.* Propositions 3.5/3.6 bound $\lambda^{-1}$ by $C$ plus a rare $\Gamma_{1/2}$ term, by discarding bad cubes (trimmed sum, Whitney partition, minimal scale separation).
*Explicit proof.* Same architecture in the planar Gaussian setting with explicit constants: a reset to an earlier completed label, planar clusters, Whitney tiles, clipped matrix averages, selected-height tails, and a positive quadratic truncation $(x-\delta)_+\le x^2/(4\delta)$. Output: the global inverse history satisfies $B^*\le\beta+R$ with $\beta=14103/10000$ and $\lVert R\rVert_{128}\le10^{-24}$, and separately $\lVert B^*\rVert_{128}\le\beta$; the local bank has $b_o=1.4732$. The reset reads the state of earlier labels only at distance at least about $260$ scales (global bank) or $300$ scales (local bank) below the current label, while the main return itself starts from the label $N-40$ (notes). The bank rests on a Gaussian tail condition on the derivative of missing shells (C14).

**C9. Gaussian heat calculus and native moment systems (class (c), (e), (d)).**
*Paper.* None of this appears; the fresh shell is reinserted with deterministic sensitivity estimates.
*Explicit proof.* At fixed $\nu\gt0$ the response is a differentiable function of Gaussian coordinates; adding a shell $a_t=a_m+\sqrt t\,j_{m+1}$ gives an exact heat identity $\frac{d}{dt}\mathbb E\Phi=\tfrac12\mathbb E\sum D^2\Phi[h_j,h_j]$ together with a two-parameter version and an exact split of the generator into center, mixed and remainder parts. The native moments at orders up to $20$ satisfy a cooperative system of $153$ positive moment inequalities, compared with an explicit Taylor-remainder enclosure (degree $160$). Returns (notes): strong history $0.9515063\lt0.9516$, single-cube norm $0.20125\lt0.2013$, buffered history $5.857\lt6.1$, buffered mean $0.3173\lt0.32$. Several of these margins are thin (the strong-history margin is about $10^{-4}$).

**C10. Vanishing bracket (class (b)).**
The native moment systems need the carré-du-champ bracket $\Gamma(T)$ of the trace defect to vanish linearly at $T=0$ for the non-constant part of the noise. The pathwise estimate $\Gamma(T)\le4\kappa_B^2B^2\,T\,F$ was supplied by the reviewers of the research notes (the original proof note was missing). Without a vanishing bracket the notes find the $L^{20}$ returns are about $1$ instead of about $0.2$ (notes). Load-bearing for the native box.

**C11. Main return (class (c), (b), (d), (e)).**
*Paper.* Lemma 3.29 localizes the defect on subcubes and Proposition 3.28 returns the bound by sensitivity estimates (Section 2.4).
*Explicit proof.* Begin from the completed coefficient $a_{N-40}$ observed on $\square_N$, with cold bound $D_{40}$. Insert the next $40$ shells one at a time. For one insertion with $f(t)=\mathbb E\,T$ at $a_t$ one proves $f'(t)\le B_0+\mathrm{aff}(t)+E_t(f(t))+I(t)$, where the right side is decreasing and concave in $f$, so it lies below a tangent at a fixed point $f_0=1/100$. On each panel of $t$ the resulting affine inequality $f'\le A_P-\ell_Pf$ is compared by an order-preserving affine flow; the $40$ maps are composed in chronological order and restored to the true frame by the one-shell factor $3^{2\gamma_0}$. The return is the native ordinary mean at $N$, to be below $\tfrac{3}{50}$.
*Numbers.* The notes' original certificate (384 panels per insertion) returns $0.0584987$. The Lean certificate (8 panels per insertion, $320$ panels in total) has a composed upper bound $\approx0.05921\lt0.06$ **(Lean)**; the value rose from $0.0585$ (384 panels, original) to $0.0592$ through a coarser panel grid and through two corrections made during formalization (Section 5.3 and Section 6). The margin is therefore about $0.0008$ (1.3 percent).
*Sharpened inequalities that decide the margin* (notes; values at the notes' earlier certificate, return $0.0589$):

| change | return | against $0.06$ |
|---|---|---|
| principal covariance coefficient $\tfrac12$ replaced by $1$ | $0.0608$ | fails |
| both quarter-turn halvings removed | $0.0605$ | fails |
| physical-flux halving removed | $0.0599694$ | passes by $3\cdot10^{-5}$ |
| directional halving removed | $0.0594$ | passes |
| the two oscillation constants $o_p,o_m$ doubled | $0.0623$ | fails |

(An earlier reviewer's float model gave $0.0585$ with the half coefficient, $0.0603$ with coefficient $1$ and $0.0662$ with an earlier payment.) The half coefficient on the principal covariance term comes from a paired Bessel estimate together with $\int\nabla h\cdot J\nabla g=0$ and the AM–GM inequality; the two other halvings use the quarter-turn invariance of the planar model (class (e)).

**C12. Passing from $\gamma_0$ to all smaller $\gamma$ (class (c)).**
The certificates are computed at $\gamma_0$. For $\gamma=\theta\gamma_0$, $0\lt\theta\le1$, the proof shows that every positive expression is dominated by $\theta$ times its endpoint value (for the main return: $E_\theta(\theta f)\le\theta E_1(f)$, then the endpoint tangent), not that signed tangent coefficients are monotone. It is genuine work but not what determines $\gamma_0$.

**C13. All-order consequence (class (a), (b)).**
*Paper.* The two-term tails are part of $\mathcal S(m,E)$.
*Explicit proof.* Given $P(n)$ at all labels, bound moments of every real order $p\ge1$: an explicit root profile (whole-root $L^4$ coefficient $2810$ from layer estimates), an averaging-and-transport inequality in finite even orders with constants $144$ (true value $36$), $19$ and $4$, and the sum over depths with the normalized factor $1-3^{-2s}$. The bulk coefficient is $\tfrac{333}{2}\cdot900000+72\cdot4350000=463050000\lt2^{29}$ (notes). A rare-term hierarchy $32\to64\to1350\to8192$ converts the moment bound into the two-term tail bound by Markov's inequality at the real order $p=u$, giving coupled witnesses $\sqrt{eA}\sqrt Z$ and $\sqrt{eB}Z^{3/2}$. The displayed denominator $1500$ in the moment bound is a weakening of the internal rate $1350$; the earlier rate $1400$ does not suffice (notes).
*Difference from the paper.* The result covers all real $p\ge1$ with $p^3$ growth in the rare term; the paper's Theorem B has $p\le C^{-1}\gamma^{-1}\lvert\log\gamma\rvert^{-1}$. It is derived after the induction rather than carried inside it.

**C14. Gaussian tail condition (class (e), (b)).**
The inverse banks and the all-order profile need a bound for the probability that the derivative of the missing shells is large, via a sharp sub-Gaussian tail $P(F-\mathbb EF\gt t)\le\exp(-t^2/(2L^2))$ with Cameron–Martin Lipschitz constants (class (e): this is Gaussian). The ceilings it imposes on $\gamma$ are in Section 5. This is the single most delicate numerical input.

**C15. Numerical certificates (class (d)).**
The finite computations (see Section 5.2) are Lean data checked by kernel reduction with exact rationals and outward interval enclosures (for roots, exponentials, logarithms, $\pi$). About a quarter of the Lean code of the repository is certificates **(Lean repository statistics: roughly $0.2$ of $0.8$ million lines)**. They replace estimates with proofs of finitely many inequalities; in no case do they replace an analytic step.

**C16. Choice of model (class (e)).**
$d=2$; the shell law is Gaussian with the explicit covariance $h^2c(\Delta x_1)c(\Delta x_2)$. This provides: the exact derivative variance ratios of $q$ (for instance $78/5$, $3432/5$, $61776$; the first derivative trace $31.2$ and second-derivative Frobenius trace $1859.52$ in the planar scalar convention); compact support, hence finite range and four-colour independence; Gaussian integration by parts, the heat identity, and sharp concentration; quarter-turn invariance in $d=2$, which produces the halvings of C11; and the Helmholtz structure that gives $c_*=h^2/(2\log3)$. It also removes the dependence on $c_*$: the explicit constants contain neither $c_*$ nor $h$ (an interpretation: the paired scaling of the field and $\nu$ leaves all normalized quantities invariant, and everything is measured relative to $B_n$ and $\nu^2$).

**C17. The bridge (class (a)).**
T3 passes from T1 to the paper's $\mathcal S(m_0,2^{16})$ by the two elementary comparisons stated in Section 2.1.

**C18. Items of the research notes that were not used.**
The research notes also contain a localized mixed inverse-Hessian lemma, a signed local Gaussian transport lemma, a nested energy gap and covariance variant, a point-centered native coefficient and a sharper all-order constant (a "coefficient 24" argument). These were developed for an earlier target ($\gamma\le3/5000$). The notes themselves describe the nested-gap and point-centered variants as valid but not adopted; none of these appears in the proof formalized here, whose all-order step has bulk coefficient $2^{29}$. They are therefore **not** among the sources of the gain; claims made about them in the notes are not formalized.

## 5. Where the gain comes from

### 5.1 The four effects

The sources do not contain an experiment that removes one change at a time from a complete proof, so the following is a judgment based on structure and on the sensitivity data of the research notes.

**Effect of tracking constants.** Necessary, because the paper's constants are only $C(d)$ and $E$. By itself it would not give a useful threshold, because the paper's architecture requires $\gamma\le E^{-10}$ and $E\ge Cc_*^{-1}\varepsilon^{-C}$ (Section 3). Tracking constants without changing the architecture gives, at best, a threshold of the order of a power of a large constant; Section 3.3 gives illustrations that are not from the sources. Class (a) items: entrance, constants of Section 2 type, the bridge.

**Effect of the architecture (new structure).** Removing $E$ from the induction (C1) and replacing contraction-plus-sensitivity by cold observation plus a 40-shell heat-flow comparison (C7, C9, C11) is what makes a threshold of the order of $10^{-4}$ conceivable. In the paper the inflation in $E$ is paid by the $\varepsilon$-contraction and finally by $E\ge c_*^{-1}\varepsilon^{-C}$, $\gamma\le E^{-10}$; in the explicit proof the only smallness is the quantity $\theta\le1$ in a box with margins of order one to ten percent. Class (c) items.

**Effect of choosing a concrete model.** Class (e) items supply the *computable* constants (exact covariances, sharp concentration, heat identity, quarter-turn symmetry). The notes show several of these are individually decisive at $\gamma_0$: both quarter-turn halvings (return $0.0605$ without), the Gaussian tail constants (ceilings below $\gamma_0$ without), the exact planar layer weights. Without the Gaussian structure the paper's sensitivity route would again carry $C(d)$.

**Effect of numerical certificates.** The certificates are what allow margins of about one percent to be claimed. They do not by themselves lower $\gamma_0$: a conservative analytic bound in place of a certified computation would typically lose a constant factor in some return, which would be repaired by lowering $\gamma_0$ (the notes' certificate layer was built so that a smaller $\gamma_0$ can be certified if a Lean constant is cruder). Class (d) items.

**Effect of genuinely new or sharper mathematics.** The sharpened inequalities (C5, C6, C10, C11) are small statements, but each is needed for a specific return to close at $\gamma_0$ (table in C11; vanishing bracket C10; boundary-charge correction below).

### 5.2 What would most reduce $\gamma_0$ if removed or weakened

All values are from the research notes and the independent reviews of them (notes), at the threshold $\gamma_0=3.4\cdot10^{-4}$.

| change | consequence reported by the sources |
|---|---|
| sharp sub-Gaussian exponent (factor $\tfrac12$, Borell–type) replaced by the planar tail condition documented in the original note, which has cruder constants | ceilings on $\gamma$ become $1.735\cdot10^{-4}$ (inverse bank) and $2.78\cdot10^{-5}$ (full-response bank), both below $\gamma_0$: fails at the notes' parameter choices |
| sharp tail replaced by a Maurey–Pisier tail ($\pi^2/8$ in the exponent) | all-order ceiling $1.449\cdot10^{-4}$, full-response $1.641\cdot10^{-4}$: fails at the notes' threshold split; the notes record that re-splitting the threshold (mean gate at $1\%$ instead of $1/2$) would give margin $1.28$ for the all-order condition, but this changes another condition and does not rescue a third step, so it is described there as new mathematics and not recommended |
| sharp tail replaced by moments plus Markov | all-order ceiling $1.316\cdot10^{-4}$, full-response $1.490\cdot10^{-4}$: fails at the notes' parameter choices |
| the actual ceilings with the sharp tail | all-order $3.576\cdot10^{-4}$ ($1.052\gamma_0$), full-response $4.049\cdot10^{-4}$ ($1.19\gamma_0$), inverse $2.531\cdot10^{-3}$ ($7.4\gamma_0$) |
| principal covariance coefficient $1$ instead of $\tfrac12$ | main return $0.0608\gt0.06$ at $\gamma_0$: fails |
| no quarter-turn halvings | main return $0.0605\gt0.06$: fails |
| no vanishing bracket | native $L^{20}$ returns about $1$ instead of $0.2$: native box does not close |
| no boundary-charge correction in the source rows | strong history $0.952235\gt0.9516$, single-cube norm $0.2018\gt0.2013$: fails |
| the two oscillation constants $o_p,o_m$ (coefficient $0.440$ and $(1+\sqrt2)\cdot0.440$) doubled together | main return $0.0623$: fails (doubling the $1/\pi$-type coefficient $0.319$ changes the return only to $0.0589323$) |

Facts from these data: the all-order tail condition has a reported ceiling of $3.576\cdot10^{-4}$, $5.2$ percent above $\gamma_0=3.4\cdot10^{-4}$, computed with the sharp constant; the full-response condition has $19$ percent and the inverse condition a factor $7.4$. Several relative margins at $\gamma_0$ are thinner than $5.2$ percent: the main return ($1.3$ percent), the scalar upper error ($0.06804$ against $0.0681$, about $0.09$ percent), the strong-history cap ($0.9515063$ against $0.9516$, about $0.01$ percent) and the single-cube cap ($0.20125$ against $0.2013$, about $0.02$ percent); the scalar lower gain has $0.002$ out of $0.31$. These are margins in value, not in $\gamma$: the sources do not compute, for any of these steps, the largest $\gamma$ for which it closes. Hence it is **not established** which step, if any, determines $\gamma_0$, nor that $\gamma_0$ is near the largest value for which the whole argument closes. (An earlier research route reported results at $\gamma\le3/5000$, above the $3.576\cdot10^{-4}$ ceiling, with different constants; its certificate could not be recovered.)

### 5.3 The main-return value across versions

The value depends on the certificate version and on the panel resolution (panels per insertion), which are separated below. Values are upper bounds for the same quantity (the native ordinary mean after the 40 insertions).

| certificate version | panels per insertion | value | status |
|---|---|---|---|
| original numerical certificate | 384 | $0.0584987$ | notes |
| after the boundary-charge correction of the source rows (a mathematical correction; lowers the value) | 384 | $0.0583833$ | notes |
| covariance residual $\sqrt{v+B_0/4}$ applied to the original | 384 | $0.0584999588$ | notes (reported in the correction itself) |
| first kernel-checked certificate | 8 | $0.0589319$ | notes; the same certificate form at 8 panels in floating point is reported as $0.058896$ |
| after the covariance-residual correction | 8 | $0.0589333$ | notes |
| after the history-slope correction (slope about $0.622$ at $\gamma_0$; an interim value $0.0591999$ with slope $0.6$ is also reported) | 8 | $0.0592116$ | **(Lean)** $5921159502433712501805269299593/10^{32}$ |

The rise from about $0.0584$ to about $0.0589$ is consistent with the coarser panel grid (8 instead of 384 panels per insertion) rather than with a correction (an inference: the notes report the 8-panel value without attributing the change); the sources do not separate this step further. The corrections of Section 6 account for $+1.2\cdot10^{-6}$ (covariance residual, at 384 panels), about $+1.4\cdot10^{-6}$ (at 8 panels) and about $+2.8\cdot10^{-4}$ (history slope, at 8 panels); the boundary-charge correction lowers the value. The final margin to $0.06$ is positive.

## 6. Corrections made during formalization

During preparation and formalization of the explicit proof, $36$ corrections to its written specification were recorded (the specification was the AI-written proof, line by line). None is a correction of the paper. The classification of their kinds below is this note's own (counts are approximate, from reading each entry):

| kind | number | examples |
|---|---|---|
| missing definition, hypothesis or dependency; statement correct once completed | $13$ | an undefined energy matrix, a bound whose variable is not defined, an inverse bank whose scope was narrower than its consumers use, an omitted use of the vanishing bracket |
| missing lemma | $5$ | the physical-flux halving, a Hessian identity on the square, a centering step, a pathwise frame inequality that was only coded |
| statement incorrect as printed, or constant imprecise | $14$ | see below |
| change of a numerical estimate or of how a bound is split | $4$ | three of them change numbers |

**Statements that were false as printed** (each repaired without changing the final constants, except where noted):

* a pathwise identity "increment $=$ old Hessian $+$ new quartic" that is false because the linear term was omitted (checked on a scalar example: $-0.3$ against $0.2$);
* a moment bound stated in $L^p$ that is false (counterexample $Y=Z^4$) and holds in the Hölder-conjugate $L^q$;
* a strict inequality that fails when the source vanishes;
* a derivative bound for the doubled matrix $A$ that is false for the constant-skew direction unless a normalization holds;
* a displayed constant $D_f=2.265+\sqrt{2.265}=3.77$ in place of the intended $\tfrac12+3^{-1/4}$;
* a rounded cap $0.9515$ used as an upper bound for a quantity equal to $0.9515063$;
* a definition of a weak history under which an identity used downstream fails;
* a displayed plateau constant ($\mu_{n-4}$ for $\mu_n$) that would give $C_D=96/(49c)-2$ instead of $96/(49c)-1$.

**Corrections that changed numbers.**

* The covariance residual carries $\sqrt{v+B_0/4}$ rather than $\sqrt v$: the identity $x^2+y^2=2v$ holds only for whole-plane projected means, not for actual finite-parent flat means. Main return: $0.0589319\to0.0589333$ (an increase of $1.4\cdot10^{-6}$).
* The history slope used by the source could not be derived from available inputs; it was replaced by a provable slope. Main return: composed to $0.0592116$ (still below $0.06$).
* A rough $L^{128/127}$ constant that rested on a bound requiring an ellipticity constant (which would have introduced $\bar\sigma/\nu$) was replaced by $R\approx150.29$; it enters only through a remainder $5\cdot10^{-24}$, and the scalar margin is unchanged to double precision.

**Errors found earlier, during the independent evaluation of the research notes** (these are errors of the AI-written proof, also not of the paper): a claim that a planar layer weight is at most $2d\,3^{-k}$ (false for $d=2$ and $k\ge2$; exact weights $8\cdot3^{-k}-32\cdot9^{-k}$; every exported number remained valid except one coded envelope, absorbed in a slack); a structural factor $1.0004$ that should be $1.0008$ in the all-order step (no number used the false value); the use of an unproved identification of a limit of expected Dirichlet energies with $\bar\sigma$ (repaired); a four-dimensional boundary-cutoff lemma whose proof diverges in $d=2$ (repaired); and a number of missing proof notes, of which the missing arguments were reconstructed or newly proved, and then reviewed.

**Errors or gaps in the paper.** None was found in the sources. In particular the paper's own statement that $c_*\le\tfrac32$ (a consequence of its assumptions) covers the passage "$E=Cc_*^{-1}\ge C_{\rm start}c_*^{-1/2}$" in the proof of Proposition 3.1. The paper states (Section 1.8) that its Lean formalization assumes $C^2$ regularity of the shells in place of $C^{1,1}$; this is a disclosed difference, not an error. The formal model in this repository also records (J2) as an assumption (Section 2.3).

## 7. Glossary

| term in the explicit proof | plain mathematics | notation in the paper |
|---|---|---|
| native | quantities of the completed coefficient $a_n=\nu I+\sum_{i\le n}j_i$ on a cube of the same or nearby scale, measured in its own true frame $\bar\sigma_n$ | $\mathcal E_{s,\infty,2}(\square_n;a_n,\bar\sigma_n)$, $s_n$; Definition 3.2 |
| native state, native box | the five moment caps (ordinary mean, strong history, single-cube norm, buffered history, buffered mean), each $\propto\theta=\gamma/\gamma_0$, together with the scalar corridor | replaces $\mathcal S(m,E)$ (Definition 3.2) |
| cold | the coefficient $a_n$ observed on a much larger cube $\square_{n+k}$ with no further shells added; how far its defect has decayed after $k$ scales | the contraction of Proposition 3.23 |
| molecular (regime) | $B_n\ll\nu^2$: the skew part is small compared with the molecular diffusivity $\nu$ | scales below $m_*$, $m_{**}$ (3.8)–(3.9) |
| molecular entrance | the statement that $P(n)$ holds for all $n\le K(\gamma,\nu,h)$ | Proposition 3.4 (base case) |
| main return | the differential inequality for $f(t)=\mathbb E\,T$ along $a_t=a_m+\sqrt t\,j_{m+1}$, composed over $40$ shells, and its output bound $\lt3/50$ | injection of the fresh layers, Proposition 3.28 and Lemma 3.29 |
| inverse bank | bound on the inverse-ellipticity history $B^*$ (the bottom block $s_*^{-1}$ of the coarse matrix, maximized over cubes and summed over depths) in $L^{128}$, with a positive split $B^*\le\beta+R$ | $\lambda_{s,q}^{-1}$, Propositions 3.5, 3.6 |
| corridor | the two-sided bound $\nu\le\bar\sigma_m$, $\tfrac{31}{50}B_m+\tfrac{19}{50}\nu^2\le\bar\sigma_m^2\le\nu^2+\tfrac{13}{8}B_m$ | (3.4) of Definition 3.2 (with constants $\tfrac14$, $4$) |
| moment caps | the numerical upper bounds of the native state, $0.06\theta$, $0.9516\theta$, $0.2013\theta$, $6.1\theta$, $0.32\theta$ | none |
| observer | the cube on which a defect is measured; "observer gap" is the number of scales between the cutoff and this cube (up to $40$) | the cube $\square_m$ in $\mathcal E_{s,\infty,2}(\square_m;\cdot)$ |
| buffer | cubes $40$ scales below the cutoff label | subcubes in the sum defining $\mathcal E_s$ |
| reset | comparing a coefficient at label $n$ with the completed coefficient at a much earlier label (at least about $260$ to $300$ scales below), so that only earlier-label state is read | the use of $\mathcal S(m-1,E)$ in Section 3.3 |
| vanishing bracket | pathwise bound of the carré-du-champ of the trace defect by $T$ times a bounded factor | none |
| $\theta$ | $\gamma/\gamma_0$ | none |
| $B_n$ | $\sum_{i\le n}h^2 3^{2\gamma i}$, accumulated shell variance | $\approx c_*\gamma^{-1}3^{2\gamma n}/(\ldots)$ |
| $T(U;a,\sigma)$ | $\sigma^{-1}\mathrm{tr}A_{11}+\sigma\mathrm{tr}A_{22}-4\ge0$ | the quantity $\mathbf J(U,\cdot,\cdot)$ maximized over loads, Lemma 2.6 and Definition 2.4 |
| positive split | $X\le b+R$ with $R\ge0$ small in $L^{128}$, used instead of a pathwise bound | $O_{\Gamma}$ tail of Proposition 3.6 |
| tail condition | the Gaussian concentration estimate for large derivatives of the missing shells | (J2) and Lemma 3.8 |

## 8. The numerical inputs and their margins (research notes unless marked)

Values at $\gamma_0=17/50000$, $\theta=1$. "Margin" is the gap between the computed upper bound and the cap that the next step consumes.

| input | computed value | consumed cap | margin | source of the value |
|---|---|---|---|---|
| cold mean, $40$ scales above the cutoff | $D_{40}=0.034265$ | used as initial value | none needed | cold recursion, $129$ lags |
| cold mean, $128$ scales above | $D_{128}=0.004746$ | $0.005$ | $2.5\cdot10^{-4}$ | same |
| global inverse bank | $A+\delta=1.41025$ | $\beta=1.4103$ | $5\cdot10^{-5}$ | positive split with $\delta=1/2000$ |
| local inverse bank | $b_o=1.4732$ | carried | | from the mean $0.1494$ after one pass |
| native strong history | $0.9515063$ (boundary-fixed rows: $0.9514991$) | $0.9516$ | about $10^{-4}$ | $153$ moment systems |
| native single-cube norm | $0.20125$ (boundary-fixed: $0.201249$) | $0.2013$ | about $5\cdot10^{-5}$ | same |
| native buffered history | $5.857$ | $6.1$ | $0.24$ | same |
| native buffered mean | $0.3173$ | $0.32$ | $0.0027$ | same |
| scalar lower gain | $K=0.31435$ | $0.312325$ | $0.0020$ | variational trial, ten error terms |
| scalar upper error | $0.068039$ | ceiling $0.0681$ | $6\cdot10^{-5}$ | long-block trial |
| scalar upper barrier | $P(0.148)=0.0021$, $P(0.90)=0.0516$ | $\gt0$ | | concave barrier |
| main return, final certificate | $0.0592116$ | $0.06$ | $0.0008$ | **(Lean)** |
| all-order bulk coefficient | $\tfrac{333}{2}\cdot900000+72\cdot4350000=463050000$ | $2^{29}=536870912$ | $14$ percent | notes |
| all-order tail condition | ceiling $3.576\cdot10^{-4}$ | $\gamma_0=3.4\cdot10^{-4}$ | $5.2$ percent | sharp sub-Gaussian tail |
| full-response bank tail condition | ceiling $4.049\cdot10^{-4}$ | $\gamma_0$ | $19$ percent | same |
| inverse bank tail condition | ceiling $2.531\cdot10^{-3}$ | $\gamma_0$ | factor $7.4$ | same |
| rare rates | internal $1350$; displayed $1500$; tail $8192$; $\log2/8192\gt2^{-48}$ | | exact margins $\tfrac{5633}{800000}$, $\tfrac{27617}{36000000}$, $\tfrac{1223}{921600000}$ | notes |
| structural frame | $3^{2\gamma_0}\lt1.0008$ | | | notes |

The quantities that the Lean repository certifies as finite computations are the following (class (d)), as described in the notes: the $320$ main-return panels with their composition; the $129$-lag cold recursion; the $153$ native moment systems with Taylor remainders; the six exact $q$ covariance caps; the exact rational gates of the inverse banks, of the all-order step and of the Gaussian tail conditions; and the scalar constants. In this note only the main-return bound was read from the Lean certificate.

## 9. Remarks on reading the numbers

* The Lean statements (Section 2) are exact. The numerical values in Sections 4 and 5 come from the research notes and from independent reviews of them, except where marked **(Lean)**; the main-return certificate was read off its Lean definition and the caps and corridor off the Lean statements; the other numerical values were not re-derived.
* A number reported by the notes at one stage may have been superseded by a later correction (Section 5.3); the final proof uses the later values.
* The comparison of Section 3.3 is the only place where estimates not from the sources appear; each is labelled.
