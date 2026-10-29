# Errata and deviations

This record lists where the Lean statements in this repository differ from the paper they formalize, and whether the paper contains any error. It is split in two. An *erratum* is a defect in the paper itself (a misprint, a wrong constant, a missing hypothesis, a false statement, or a printed step that does not prove what it claims). A *deviation* is a deliberate difference that is not an error of the paper: a restriction of scope, a reformulation, an explicit parameter window in place of "sufficiently small", or a different proof route. A gap is called an erratum only when a printed assertion is false; a supplied argument for a true step is listed as a deviation or not at all.

**Source.** S. Armstrong, A. Bou-Rabee, T. Kuusi, *Superdiffusion and anomalous regularization in self-similar random incompressible flows*, arXiv:2601.22142v2 (called "the paper"). Locations are given by section, result number and equation number of arXiv v2, with the page of v2 where helpful.

**Counting.** Entries are counted, not occurrences. Conventions inherited from the public Lean formalization of the paper, [`Algsuperdiff`](https://github.com/scottnarmstrong/Superdiffusion), which this repository builds on without modification, are credited to it and not counted here unless they change the statements below. One such convention is the assumption of $C^2$ regularity of the shells in place of $C^{1,1}$ in (J2); the paper itself discloses it in Section 1.8.

**Result.** No erratum of the paper was found, and none affects the main theorems `explicit_induction_bounds` and `inductionState_of_explicit`. There are eight deviations. Together they say: the Lean theorems cover one concrete model in dimension 2, are implications over that model class (the existence of the model is not formalized), give an explicit threshold $\gamma \le 17/50000$ for part of Proposition 3.1, and reach the paper's induction hypothesis through a different induction state.

Intermediate statements of the formal development were corrected along the way; these concern the development, not the paper, and are not listed here.

| Source | Errata | Deviations |
|---|---|---|
| Armstrong, Bou-Rabee, Kuusi, arXiv:2601.22142v2 | 0 | 8 |

## Armstrong, Bou-Rabee, Kuusi, arXiv:2601.22142v2

### Errata

None.

### Deviations

| # | Location | Kind | Lean statement |
|---|---|---|---|
| 1 | Section 1.5, (J1)–(J4); Proposition 3.1 | scope | all main theorems |
| 2 | Section 1.5; Proposition 3.1 | reformulation | all main theorems |
| 3 | Proposition 3.1, Definition 3.2, (3.6) | explicit window | all main theorems |
| 4 | Proposition 3.1, (3.2)–(3.3) | partial coverage | `explicit_induction_bounds` |
| 5 | Definition 3.2, (3.4)–(3.7) | explicit constant | `inductionState_of_explicit` |
| 6 | Definition 3.2; Sections 3.3–3.6 | different induction state | `nativeInductionState`, three intermediate theorems |
| 7 | Theorem B, (1.12); Proposition 3.1, (3.2) | reformulation | `AllOrderBounds` |
| 8 | Theorems A, B, C | not made explicit | none |

**1. Section 1.5, assumptions (J1)–(J4); Proposition 3.1 (p. 58).** *Scope.* The paper treats every dimension $d \ge 2$ and every shell law satisfying (J1)–(J4). The Lean theorems treat $d = 2$ and one shell law, the planar $q \otimes q$ Gaussian law: the scalar stream $\psi$ of the skew shell $j_0 = \psi J$ is a centered Gaussian field with covariance $h^2\, c(x_1)\, c(x_2)$, where $c$ is the autocorrelation of $q(x) = \sqrt{3003/1024}\,(1-4x^2)^3\,\mathbf 1_{\lvert x\rvert \le 1/2}$. This is the hypothesis `PlanarQ3Gaussian`, with kernel `q3Kernel` and covariance `q3Cov`. *Effect.* Every main statement carries `(M : ABKModel 2)` and `(hM : PlanarQ3Gaussian M h)`; nothing is claimed for other dimensions or other kernels. See [`PlanarQ3Gaussian.lean`](../ASDExplicitGamma/Statements/PlanarQ3Gaussian.lean), [`Q3Kernel.lean`](../ASDExplicitGamma/Statements/Q3Kernel.lean), [`Q3Cov.lean`](../ASDExplicitGamma/Statements/Q3Cov.lean).

**2. Section 1.5; Proposition 3.1 (p. 58).** *Form of the statements.* The paper's results are statements about the random environment of a given shell law. The Lean theorems are implications: for every `M : ABKModel 2` (a model in the sense of the paper's standing assumptions, in the formulation of `Algsuperdiff`) with `PlanarQ3Gaussian M h`, the conclusion holds. No model satisfying this hypothesis is constructed in Lean, so existence (white noise convolved with the kernel, the tail condition (J2), the nondegeneracy (J4)) is not formalized, and the theorems would be vacuous if no such model existed. *Effect.* The hypotheses of `explicit_induction_bounds`, `inductionState_of_explicit`, `molecular_entrance`, `induction_step` and `allorder_of_state` all have this form. See [`ExplicitInductionBounds.lean`](../ASDExplicitGamma/Statements/ExplicitInductionBounds.lean).

**3. Proposition 3.1 (p. 58), Definition 3.2, condition (3.6) (p. 58).** *Explicit window.* The paper requires $\gamma \le C^{-10}c_*^{10}$ with an unspecified constant $C(d)$, inside the standing range $\gamma \in (0, 1/4]$ of Section 1.5. The Lean theorems assume $\gamma \le 17/50000$, a number independent of $\nu$, of the amplitude $h$ and of $c_*$ (`gammaZero`). *Effect.* Hypothesis `M.gamma ≤ 17 / 50000` (or `M.gamma ≤ gammaZero`) in each main statement. See [`GammaZero.lean`](../ASDExplicitGamma/Statements/GammaZero.lean) and [`Theta.lean`](../ASDExplicitGamma/Statements/Theta.lean) (`theta`, the ratio $\gamma/\gamma_0$).

**4. Proposition 3.1, (3.2) and (3.3) (p. 58).** *Partial coverage.* Proposition 3.1 has two conclusions: the two-term tail bound (3.2) on $\mathcal E_{s,\infty,2}(\square_m; \mathbf a_m, \bar\sigma_m)$ and the sharp asymptotics (3.3) of $\bar\sigma_m$ with relative error $C c_*^{-2}\gamma^{1/2}\lvert\log\gamma\rvert$. The Lean theorem `explicit_induction_bounds` covers the analogue of (3.2) with explicit constants, and a corridor for $\bar\sigma_m$ at the level of (3.4): $\nu \le \bar\sigma_m$ and $\tfrac{31}{50}B_m + \tfrac{19}{50}\nu^2 \le \bar\sigma_m^2 \le \nu^2 + \tfrac{13}{8}B_m$, with $B_m$ the accumulated shell variance (`shellVarianceSum`). It does not prove (3.3). *Effect.* No statement in this repository gives an explicit version of (3.3). See [`ExplicitInductionBounds.lean`](../ASDExplicitGamma/Statements/ExplicitInductionBounds.lean) and [`ShellVarianceSum.lean`](../ASDExplicitGamma/Statements/ShellVarianceSum.lean).

**5. Definition 3.2, (3.4), (3.5); conditions (3.6), (3.7) (p. 58).** *Choice of $E$.* The paper's induction hypothesis $\mathcal S(m_0, E)$ carries a free parameter $E$, and its propagation (3.7) is proved for $E \ge C c_*^{-1}$ and $\gamma \le E^{-10}$. The Lean theorem `inductionState_of_explicit` proves the predicate `Algsuperdiff.Frozen.Section3.inductionState` (the Lean form of $\mathcal S(m_0,E)$ from `Algsuperdiff`) at the single value $E = 2^{16}$, for every $m_0 \in \mathbb Z$ and every $\gamma \le 17/50000$. The condition $\gamma \le E^{-10}$ of (3.6) is not assumed, and for $\gamma$ near $17/50000$ it fails; it is not used. *Effect.* The theorem gives (3.4) and (3.5) at $E = 2^{16}$; it does not make the paper's step (3.7) or any downstream statement that consumes $\mathcal S(m,E)$ under (3.6) explicit. See [`InductionStateOfExplicit.lean`](../ASDExplicitGamma/Statements/InductionStateOfExplicit.lean).

**6. Definition 3.2; Sections 3.3–3.6.** *Different induction state.* The paper propagates $\mathcal S(m,E)$. This repository propagates a different state `nativeInductionState`: five numerical caps on moments of the normalized trace defect (`ordinaryMean`, `strong20`, `root20`, `buffer40History`, `bufferMean`), each proportional to $\theta = \gamma/\gamma_0$, together with the corridor for $\bar\sigma_n$. The three intermediate theorems are `molecular_entrance` (the state holds at all sufficiently negative labels, the analogue of the base case, Proposition 3.4), `induction_step` (the state at $N$ follows from the state at all earlier labels) and `allorder_of_state` (the state at every label gives the tail and moment bounds of item 4 of `explicit_induction_bounds`). The paper's tail bounds are not carried through the induction here; they are derived from the state afterwards. *Effect.* These statements are about `nativeInductionState`, not about the predicate of Definition 3.2. The comparison of the two states is in [CHANGES-FROM-THE-PAPER.md](CHANGES-FROM-THE-PAPER.md). See [`NativeInductionState.lean`](../ASDExplicitGamma/Statements/NativeInductionState.lean), [`MolecularEntrance.lean`](../ASDExplicitGamma/Statements/MolecularEntrance.lean), [`InductionStep.lean`](../ASDExplicitGamma/Statements/InductionStep.lean), [`AllorderOfState.lean`](../ASDExplicitGamma/Statements/AllorderOfState.lean), and the definitions [`OrdinaryMean.lean`](../ASDExplicitGamma/Statements/OrdinaryMean.lean), [`Strong20.lean`](../ASDExplicitGamma/Statements/Strong20.lean), [`Root20.lean`](../ASDExplicitGamma/Statements/Root20.lean), [`Buffer40History.lean`](../ASDExplicitGamma/Statements/Buffer40History.lean), [`BufferMean.lean`](../ASDExplicitGamma/Statements/BufferMean.lean), [`TraceDefect.lean`](../ASDExplicitGamma/Statements/TraceDefect.lean), [`CutoffTraceDefect.lean`](../ASDExplicitGamma/Statements/CutoffTraceDefect.lean).

**7. Theorem B, (1.12) (p. 6); Proposition 3.1, (3.2) (p. 58).** *Moment form of the all-order bound.* Proposition 3.1 states its error bound only as a two-term Orlicz tail bound, and Theorem B states moments of its error variable for $p \in [1, C^{-1}\gamma^{-1}\lvert\log\gamma\rvert^{-1}]$. The predicate `AllOrderBounds` states, for every $s \in [8\gamma, 1]$, both (a) the two-term $\Gamma_2/\Gamma_{1/2}$ bound $\mathcal E_s \le O_{\Gamma_2}(2^{16}\sqrt\gamma / s) + O_{\Gamma_{1/2}}(e^{-\log 2/(8192\gamma)})$ and (b) for every real $p \ge 1$ the moment bound $\lVert \mathcal E_s^2\rVert_{L^p} \le 2^{29}\gamma p/s^2 + e^{-\log 2/(1500\gamma)}\,p^3$. The moment bound is an addition to what the paper states for $\mathcal E_{s,\infty,2}$, with an explicit range of $p$ that is all of $[1,\infty)$. *Effect.* Item 4 of `explicit_induction_bounds` and the conclusion of `allorder_of_state`. See [`AllOrderBounds.lean`](../ASDExplicitGamma/Statements/AllOrderBounds.lean).

**8. Theorems A, B and C (pp. 5, 6, 8).** *Not made explicit.* The paper derives Theorems A (quenched superdiffusivity), B (renormalization of the generator) and C (anomalous Hölder regularity) from Proposition 3.1, each with unspecified constants $\gamma_0(d,c_*)$ and $C(d,c_*)$. The theorems of this repository do not give explicit versions of any of them, and the existing statements of `Algsuperdiff` that consume $\mathcal S(m,E)$ under (3.6) are not applied to the state of deviation 5. *Effect.* None of the main statements concerns the process of Theorem A, the quantity of Theorem B or the regularity of Theorem C.


## How the proof route differs

The paper closes its induction with a free constant $E$ that is inflated at every step and paid for by a contraction estimate (Proposition 3.23), which is why it needs $\gamma \le E^{-10}$. The formal proof carries instead a box of numerical caps scaling with $\gamma/\gamma_0$ and closes it directly with numerical constants. It uses the Gaussian structure of the planar model (an exact heat-flow identity for adding a shell, exact covariance constants of $q$, sharp Gaussian concentration, quarter-turn symmetry) in place of the paper's generic sensitivity and Orlicz estimates, and it verifies finitely many numerical inequalities by kernel-checked computation. The paper contains no error that this route repairs. The route is described step by step, with the correspondence to the paper's Sections 3.3–3.6, in [CHANGES-FROM-THE-PAPER.md](CHANGES-FROM-THE-PAPER.md).

## Outside scope

- Existence of a model satisfying `ABKModel 2` and `PlanarQ3Gaussian` (deviation 2).
- Dimensions other than 2 and kernels other than $q \otimes q$ (deviation 1).
- The sharp asymptotics (3.3) of $\bar\sigma_m$ (deviation 4).
- Explicit versions of Theorems A, B and C, and of the sections of the paper between Proposition 3.1 and these theorems (deviation 8).
- The research notes' common higher-cutoff inverse bound is not formalized.
- A claim that $17/50000$ is the largest threshold for which the argument closes.

## References used only as background

- The quantitative homogenization theory and the earlier work on the borderline case $\gamma = 0$ cited in the paper as the source of its coarse-graining framework (the paper's own references).
- [`Algsuperdiff`](https://github.com/scottnarmstrong/Superdiffusion), the Lean formalization of the paper, from which the model structure `ABKModel` and the induction predicate are taken.
