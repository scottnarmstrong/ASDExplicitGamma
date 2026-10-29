# An explicit threshold for the superdiffusion induction

[![Build and verify](https://github.com/scottnarmstrong/ASDExplicitGamma/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/scottnarmstrong/ASDExplicitGamma/actions/workflows/build.yml)

This repository is built on [Superdiffusion](https://github.com/scottnarmstrong/Superdiffusion), the Lean 4
formalization of

> Scott Armstrong, Ahmed Bou-Rabee and Tuomo Kuusi,
> [*Superdiffusion and anomalous regularization in self-similar random incompressible flows*](https://arxiv.org/abs/2601.22142),
> arXiv:2601.22142v2.

The paper's theorems hold for all sufficiently small values of the self-similarity exponent `γ`. The paper and its
formalization prove that such a threshold exists, but do not compute it. The heart of the argument is a
renormalization induction over scales: Proposition 3.1 of the paper, whose induction hypothesis is Definition 3.2.

**This repository proves the renormalization induction with an explicit threshold, `γ ≤ γ₀ = 17/50000 = 0.00034`,
for one concrete model:** the planar `q ⊗ q` Gaussian model. It does not make explicit the thresholds of the paper's
main theorems (Theorems A, B and C), which use further steps.

The theorems are stated about the objects of the Superdiffusion formalization, which is a pinned, unmodified Lake
dependency: the model `ABKModel 2`, the effective diffusivity `Annealed.sigmaBar`, the homogenization error
`Observable.cutoffHomogenizationError`, and the paper's induction hypothesis `Algsuperdiff.Frozen.Section3.inductionState`.

## What is proved

**The model.** `M : ABKModel 2` is a model of the paper in dimension 2: a stream matrix that is a sum of independent
shells over all triadic scales, with exact self-similar scaling of exponent `γ = M.gamma`, molecular diffusivity
`ν = M.nu > 0`, and the paper's standing assumptions. The hypothesis `PlanarQ3Gaussian M h` says that the scalar stream
`ψ` of one shell is a centered Gaussian field with covariance

> `E[ψ(x) ψ(y)] = h² c(x₁ − y₁) c(x₂ − y₂)`,  `c(u) = ∫ q(z) q(z + u) dz`,  `q(x) = √(3003/1024) (1 − 4x²)³` on `|x| ≤ ½`,

for an amplitude `h > 0` (the definitions `PlanarQ3Gaussian`, `q3Cov` and `q3Kernel`). Write
`B_m = h² 3^{2γm}/(1 − 3^{−2γ})` for the accumulated shell variance (`shellVarianceSum`) and `σ̄_m` for the effective
diffusivity at scale `3^m`.

**Theorem T1** (`explicit_induction_bounds`). If `γ ≤ 17/50000`, then at every scale `m ∈ ℤ`:

- the diffusivity stays in an explicit corridor,
  `ν ≤ σ̄_m` and `(31/50) B_m + (19/50) ν² ≤ σ̄_m² ≤ ν² + (13/8) B_m`;
- for every `s ∈ [8γ, 1]`, the homogenization error `E_s` of the cutoff coefficient on the cube of side `3^m`
  satisfies the two-term tail bound `E_s ≤ O_{Γ₂}(2¹⁶ √γ / s) + O_{Γ_{1/2}}(exp(−log 2 / (8192 γ)))`;
- and, for every real `p ≥ 1`, the moment bound `‖E_s²‖_{Lᵖ} ≤ 2²⁹ γ p / s² + exp(−log 2 / (1500 γ)) p³`.

```lean
theorem explicit_induction_bounds (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ 17 / 50000) (m : ℤ) :
    M.nu ≤ (Annealed.sigmaBar M m : ℝ) ∧
    (31 / 50) * shellVarianceSum h M.gamma m + (19 / 50) * M.nu ^ 2 ≤
      (Annealed.sigmaBar M m : ℝ) ^ 2 ∧
    (Annealed.sigmaBar M m : ℝ) ^ 2 ≤ M.nu ^ 2 + (13 / 8) * shellVarianceSum h M.gamma m ∧
    AllOrderBounds M m
```

The last two bounds are the definition `AllOrderBounds`, in
[`Statements/AllOrderBounds.lean`](ASDExplicitGamma/Statements/AllOrderBounds.lean).

**Theorem T3** (`inductionState_of_explicit`). Under the same hypotheses, the induction hypothesis of the paper
(Definition 3.2), in the form of the Superdiffusion formalization, holds at every scale with the constant `E = 2¹⁶`:

```lean
theorem inductionState_of_explicit (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ 17 / 50000) (m0 : ℤ) :
    Algsuperdiff.Frozen.Section3.inductionState M m0 ⟨2 ^ 16, by norm_num⟩
```

**The induction.** T1 is proved by an induction over scales on a state `P(n)` (`nativeInductionState`):

- five moments of the normalized trace defect of the coarse-grained matrices are bounded by caps proportional to
  `θ = γ/γ₀`;
- together with the corridor.

The induction rests on three intermediate theorems, also stated as separate files:

| Theorem | Statement |
|---|---|
| `molecular_entrance` | `P(n)` holds for every `n ≤ K`, for some `K` (the small-scale, molecular regime) |
| `induction_step` | if `P(n)` holds for every `n < N`, then `P(N)` holds |
| `allorder_of_state` | if `P(n)` holds for every `n`, the bounds `AllOrderBounds` hold at every scale |

All 5 theorems and the 15 definitions they use are in [`ASDExplicitGamma/Statements/`](ASDExplicitGamma/Statements/),
one per file. Their proofs are assembled in [`ASDExplicitGamma/StatementProofs/`](ASDExplicitGamma/StatementProofs/).
Each of the five theorems depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`, and the library
contains no `sorry`.

### What is not proved

- **Existence of the model.** T1 and T3 are implications: they hold for every model of `ABKModel 2` that satisfies
  `PlanarQ3Gaussian`. Constructing such a model, that is, white noise convolved with the kernel together with the
  standing assumptions, is not part of this repository.
- **The paper's main theorems.** The sharp asymptotics (3.3) of `σ̄_m` and Theorems A, B and C are not made explicit.
  The Superdiffusion formalization proves them from the induction hypothesis for `γ ≤ E⁻¹⁰` and further non-explicit
  conditions, so T3 does not make them explicit by itself.
- **Other models and dimensions.** Only `d = 2` and this Gaussian model are covered.

## How the proof differs from the paper

The proof formalized here is not the paper's argument with constants tracked. The paper carries a free constant `E`
through its induction and closes it by taking `γ ≤ E⁻¹⁰`. The explicit proof instead:

- carries a box of numerical caps;
- uses the Gaussian structure of the model (an exact heat-flow identity for adding one shell, exact covariances,
  sharp concentration, quarter-turn symmetry);
- relies on a few sharpened inequalities;
- checks its thin margins by exact numerical certificates.

[`docs/CHANGES-FROM-THE-PAPER.md`](docs/CHANGES-FROM-THE-PAPER.md) compares the two proofs step by step and assesses
where the explicit threshold comes from.

## Errata and deviations

[`docs/ERRATA-AND-DEVIATIONS.md`](docs/ERRATA-AND-DEVIATIONS.md) records where the Lean statements differ from the
paper:

| Source | Errata | Deviations |
|---|---|---|
| arXiv:2601.22142v2 | 0 | 8 |

No erratum of the paper was found. The deviations are choices of scope:

- the planar Gaussian model;
- the explicit window `γ ≤ 17/50000` in place of "`γ` small enough";
- a different induction state;
- the all-order bound for every real `p ≥ 1`;
- the parts of the paper that are not made explicit.

## Repository layout

| Path | Content |
|---|---|
| [`ASDExplicitGamma/Statements/`](ASDExplicitGamma/Statements) | the 5 theorems and the 15 definitions they use, one per file |
| [`ASDExplicitGamma/StatementProofs/`](ASDExplicitGamma/StatementProofs) | the proofs of the 5 theorems, assembled from the library |
| `Model/`, `Gaussian/`, `Variational/`, `Triadic/`, `Response/` | the model, Gaussian calculus, the variational and transport toolkit |
| `Cold/`, `Scalar/`, `Inverse/`, `Native/`, `Main/`, `AllOrder/`, `Joint/`, `Bridge/` | the parts of the proof: cold start, scalar corridor, inverse estimates, native moment systems, main return, all-order consequence, induction step, bridge to the paper |
| `Numerics/` | the numerical certificates: exact rational and interval computations checked by the Lean kernel |
| [`docs/PROOF-MAP.md`](docs/PROOF-MAP.md) | the steps of the proof, with the Lean files that prove them; the step labels in comments refer to it |
| [`ASDExplicitGammaAudit/Axioms.lean`](ASDExplicitGammaAudit/Axioms.lean) | the axiom report of the five theorems |

The library has about 6,800 modules and 0.8 million lines; about a quarter are numerical certificates.

## Building and verifying

You need [elan](https://github.com/leanprover/elan), about 40 GB of disk, and at least 16 GB of memory. The heaviest
certificate modules need up to 6 GB each.

```bash
git clone https://github.com/scottnarmstrong/ASDExplicitGamma.git
cd ASDExplicitGamma
lake exe cache get      # Mathlib's prebuilt oleans
```

The source dependencies are CoarseGraining, MarkovProcess and Superdiffusion, at the commits pinned in
`lake-manifest.json`. Either compile them, which takes a few hours:

```bash
lake build @CoarseGraining @MarkovProcess @superdiffusion_formalization
```

or download their prebuilt outputs from this repository's
[`dependency-oleans`](https://github.com/scottnarmstrong/ASDExplicitGamma/releases/tag/dependency-oleans) release. This
is what CI does. The last command checks that they are current for the pinned sources, without compiling anything:

```bash
key=$(python3 scripts/deps_key.py)
gh release download dependency-oleans -R scottnarmstrong/ASDExplicitGamma -p "deps-$key.tar.zst*"
sha256sum -c "deps-$key.tar.zst.sha256"
zstd -dc "deps-$key.tar.zst" | tar -x
lake build --no-build @CoarseGraining @MarkovProcess @superdiffusion_formalization
```

Then build the library and the axiom report:

```bash
lake build                          # about 13 CPU-hours in total
lake build ASDExplicitGammaAudit 2>&1 | tee axioms.log
python3 scripts/check_axioms.py axioms.log ASDExplicitGammaAudit/Axioms.lean
```

The axiom report must list exactly `propext`, `Classical.choice` and `Quot.sound` for each of the five theorems.

**Continuous integration** ([`build.yml`](.github/workflows/build.yml)) runs on every push.
- The library is too large for a single 6-hour job of a hosted runner, so the workflow builds it in four stages of
  parallel jobs. They are planned from the import graph by [`scripts/ci_plan.py`](scripts/ci_plan.py) and pass their
  build outputs on to the next stage.
- The last job builds the rest of the library with `lake build` and fails on any `sorry`. It also checks that every
  file is a Lean module and runs the axiom report.
- Mathlib comes from its cache, and the three source dependencies from the `dependency-oleans` release.
  [`dependency-oleans.yml`](.github/workflows/dependency-oleans.yml) produces that release.

## How this formalization was made

The explicit proof was developed with AI assistance, starting from the paper's argument. Its research notes are not
part of this repository; [`docs/CHANGES-FROM-THE-PAPER.md`](docs/CHANGES-FROM-THE-PAPER.md) describes the resulting
proof.

The Lean formalization was written by AI agents under the authors' supervision, in this order:

1. Scott Armstrong approved the statements of the five theorems and the fifteen definitions before any of them was
   proved.
2. Independent agent reviews compared each statement with the paper.
3. Each completed proof of a main statement received a separate audit.

[`formalization.yaml`](formalization.yaml) lists the models and tools used. The Lean kernel checks every proof,
including the numerical certificates.

## Citation and license

If you use this formalization, please cite it as described in [`CITATION.cff`](CITATION.cff), and cite the paper. The
code is released under the Apache License 2.0 ([`LICENSE`](LICENSE)).

## Acknowledgements

This repository is built on Lean 4, Mathlib, Lake, and the CoarseGraining, MarkovProcess and Superdiffusion libraries.
Scott Armstrong and Tuomo Kuusi were supported by the European Research Council (ERC) under the European Union's
Horizon Europe research and innovation programme, grant agreement No. 101200828.
