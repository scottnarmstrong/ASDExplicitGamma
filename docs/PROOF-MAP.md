# Proof map

The proof of the main theorems is organized in steps, the nodes of a dependency graph. This page lists
them by part. Labels such as `MA-E-COVARIANCE` in the comments of the library refer to this list. For
each step it gives its title, the steps it uses, and the Lean files where it is proved, when they are
single files. A step without files is proved inside the files of the steps that use it.

## Main theorems

| Step | Title | Uses | Lean |
|---|---|---|---|
| `ROOT-T1` | Explicit induction bounds (`explicit_induction_bounds`) | `GATE-ENTRANCE`, `GATE-STEP`, `GATE-ALLORDER`, `DEF-NATIVE-STATE`, `DEF-SHELL-VARIANCE`, `DEF-ALLORDER-BOUNDS`, `DEF-GAMMA-ZERO` | [`ExplicitInductionBounds.lean`](../ASDExplicitGamma/Statements/ExplicitInductionBounds.lean), [`ExplicitInductionBounds.lean`](../ASDExplicitGamma/StatementProofs/ExplicitInductionBounds.lean) |
| `ROOT-T3` | The paper's induction state with E = 2¹⁶ (`inductionState_of_explicit`) | `ROOT-T1`, `BR-T3-INDUCTION-STATE`, `DEF-ALLORDER-BOUNDS`, `MO-J4-CSTAR`, `DEF-GAMMA-ZERO` | [`InductionStateOfExplicit.lean`](../ASDExplicitGamma/Statements/InductionStateOfExplicit.lean), [`InductionStateOfExplicit.lean`](../ASDExplicitGamma/StatementProofs/InductionStateOfExplicit.lean) |

## Intermediate theorems

| Step | Title | Uses | Lean |
|---|---|---|---|
| `GATE-ALLORDER` | All-order consequence (`allorder_of_state`) | `AO-ALL-PROFILE`, `AO-OBSERVABLE-ADAPTER`, `AO-HISTORY-SUM`, `AO-MARKOV-COUPLED`, `IN-AO-ORDER-RESET`, `VA-TRUE-FRAME-MEAN`, `SC-STRUCTURAL-CONTINUITY`, `NU-AO-FRAME-GATES`, `NU-AO-RARE-RATES`, `DEF-ALLORDER-BOUNDS`, `DEF-NATIVE-STATE` | [`AllorderOfState.lean`](../ASDExplicitGamma/Statements/AllorderOfState.lean), [`AllorderOfState.lean`](../ASDExplicitGamma/StatementProofs/AllorderOfState.lean) |
| `GATE-ENTRANCE` | Molecular entrance (`molecular_entrance`) | `JO-MOLECULAR-BASE`, `NA-MOLECULAR-BOX`, `SC-ENTRANCE-MOLECULAR-STARTUP`, `SC-MOLECULAR-FIVE-FOUR`, `DEF-NATIVE-STATE` | [`MolecularEntrance.lean`](../ASDExplicitGamma/Statements/MolecularEntrance.lean) |
| `GATE-STEP` | Induction step (`induction_step`) | `JO-STEP-ASSEMBLY`, `JO-LOWER-SCALAR-N`, `JO-ORDINARY-MEAN`, `JO-STRONG20-N`, `JO-ROOT20-N`, `JO-BUFFER40-HISTORY-N`, `JO-BUFFER40-MEAN-N`, `JO-UPPER-SCALAR-N`, `DEF-NATIVE-STATE` | [`InductionStep.lean`](../ASDExplicitGamma/Statements/InductionStep.lean), [`InductionStep.lean`](../ASDExplicitGamma/StatementProofs/InductionStep.lean) |

## Bridge to the induction state of the paper

| Step | Title | Uses | Lean |
|---|---|---|---|
| `BR-T3-INDUCTION-STATE` | Pointwise T1 corridor/all-order bridge to T3 | `DEF-ALLORDER-BOUNDS`, `NU-BRIDGE-RATIO`, `EXT-Algsuperdiff-Frozen-Section3-inductionState`, `EXT-Homogenization-IndependentSums-IsBigOWith-mono-scale` | [`T3.lean`](../ASDExplicitGamma/Bridge/T3.lean) |

## Definitions

| Step | Title | Uses | Lean |
|---|---|---|---|
| `DEF-ALLORDER-BOUNDS` | All-order conclusion | `EXT-Algsuperdiff-Section3-Observable-cutoffHomogenizationError`, `EXT-Homogenization-IndependentSums-gammaSigma`, `EXT-Algsuperdiff-Section3-Probability-IsTwoTermBigOWith`, `EXT-Algsuperdiff-Section3-Cutoff-cutoffSampleLaw` |  |
| `DEF-BUFFER-MEAN` | Five carried observables | `DEF-CUTOFF-TRACE-DEFECT`, `EXT-Algsuperdiff-Section3-Cutoff-cutoffSampleLaw` |  |
| `DEF-BUFFER40-HISTORY` | Five carried observables | `DEF-CUTOFF-TRACE-DEFECT`, `EXT-Algsuperdiff-Section3-Cutoff-cutoffSampleLaw` |  |
| `DEF-CUTOFF-TRACE-DEFECT` | Completed-cutoff observable | `DEF-TRACE-DEFECT`, `EXT-Algsuperdiff-Section3-Cutoff-coefficientCutoff`, `EXT-Algsuperdiff-Section3-Annealed-sigmaBar`, `EXT-Homogenization-cubeSet` |  |
| `DEF-GAMMA-ZERO` | Endpoint and proportional parameter |  |  |
| `DEF-MA-LOADS-AND-SLOPES` |  | `DEF-THETA` |  |
| `DEF-NATIVE-STATE` | Joint induction state | `DEF-ORDINARY-MEAN`, `DEF-STRONG20`, `DEF-ROOT20`, `DEF-BUFFER40-HISTORY`, `DEF-BUFFER-MEAN`, `DEF-SHELL-VARIANCE`, `DEF-THETA`, `EXT-Algsuperdiff-Section3-Annealed-sigmaBar` |  |
| `DEF-ORDINARY-MEAN` | Five carried observables | `DEF-CUTOFF-TRACE-DEFECT`, `EXT-Algsuperdiff-Section3-Cutoff-cutoffSampleLaw` |  |
| `DEF-PLANAR-Q3-GAUSSIAN` | Finite-dimensional shell law | `DEF-Q3-COV`, `EXT-Algsuperdiff-Frozen-Assumptions-ShellField-zeroShellLaw` |  |
| `DEF-Q3-COV` | Autocovariance | `DEF-Q3-KERNEL` |  |
| `DEF-Q3-KERNEL` | One-dimensional q3 kernel |  |  |
| `DEF-ROOT20` | Five carried observables | `DEF-CUTOFF-TRACE-DEFECT`, `EXT-Algsuperdiff-Section3-Cutoff-cutoffSampleLaw` |  |
| `DEF-SHELL-VARIANCE` | Accumulated scalar variance |  |  |
| `DEF-STRONG20` | Five carried observables | `DEF-CUTOFF-TRACE-DEFECT`, `EXT-Algsuperdiff-Section3-Cutoff-cutoffSampleLaw` |  |
| `DEF-THETA` | Endpoint and proportional parameter | `DEF-GAMMA-ZERO` |  |
| `DEF-TRACE-DEFECT` | Four-load trace defect | `EXT-Homogenization-coarseBlockMatrix` |  |
| `DEF-WAVE-GATE-CONSTANTS` | Exact q3 derivative and wave-gate constants | `MO-Q3-DERIVATIVE-MOMENTS` |  |

## The model

| Step | Title | Uses | Lean |
|---|---|---|---|
| `MO-AMPLITUDE-INVARIANCE` | Paired disorder and diffusivity scaling | `EXT-Homogenization-blockMatrixOfCoeff`, `DEF-TRACE-DEFECT`, `DEF-SHELL-VARIANCE`, `DEF-THETA`, `MO-COARSE-CONGRUENCE` |  |
| `MO-BFLAT-CAPS` | Six q3 harmonic-defect caps | `MO-Q3-IDENTITIES`, `NU-MO-BFLAT-CAPS`, `EXT-Orthonormal-sum-inner-products-le`, `MO-BFLAT-TAIL` |  |
| `MO-BFLAT-TAIL` | All-depth monotone tail of the q3 harmonic-defect cap | `MO-Q3-IDENTITIES` |  |
| `MO-COARSE-CONGRUENCE` | Coarse-matrix congruence under coefficient scaling | `EXT-Homogenization-blockMatrixOfCoeff`, `EXT-Homogenization-coarseBlockMatrix` |  |
| `MO-CUTOFF-IDENTIFICATION` | Completed law and partial insertion | `EXT-Algsuperdiff-Section3-Cutoff-coefficientCutoff`, `EXT-Algsuperdiff-Section3-Cutoff-cutoffSampleLaw`, `EXT-Algsuperdiff-Frozen-Assumptions-ShellLawPrefix-independent`, `EXT-Algsuperdiff-Frozen-Assumptions-ShellLawPrefix-marginal-scaling`, `EXT-Algsuperdiff-Section3-Cutoff-CutoffSample`, `DEF-PLANAR-Q3-GAUSSIAN` |  |
| `MO-FOUR-COLOR` | Four-colour averaging from Gaussian locality | `MO-LOCAL-INDEPENDENCE`, `GA-RIO`, `CO-EXACT-CENTERING` |  |
| `MO-HELMHOLTZ-MULTIPLIER` | Helmholtz multiplier and directional symmetry | `MO-SPECTRAL-ISOMETRY`, `MO-Q3-IDENTITIES` | [`SpectralHelmholtzProjection.lean`](../ASDExplicitGamma/Model/SpectralHelmholtzProjection.lean) |
| `MO-J4-CSTAR` | Planar nondegeneracy constant | `MO-HELMHOLTZ-MULTIPLIER`, `MO-SPECTRAL-ISOMETRY`, `MO-Q3-IDENTITIES`, `DEF-PLANAR-Q3-GAUSSIAN`, `EXT-Algsuperdiff-Frozen-Assumptions-ShellField-zeroShellPotentialCorrector`, `EXT-Algsuperdiff-Section3-Disorder-cstar-characterization` | [`Cstar.lean`](../ASDExplicitGamma/Model/Cstar.lean) |
| `MO-LOCAL-INDEPENDENCE` | Gaussian locality and shell independence | `DEF-PLANAR-Q3-GAUSSIAN`, `MO-Q3-IDENTITIES`, `MO-SHELL-SCALING`, `EXT-Algsuperdiff-Frozen-Assumptions-ShellLawPrefix-independent`, `MO-CUTOFF-IDENTIFICATION` |  |
| `MO-PRODUCT-Q3-D4-GAUGE` | Cell rotation symmetry and stationary gauge | `DEF-PLANAR-Q3-GAUSSIAN`, `MO-Q3-IDENTITIES`, `MO-SHELL-SCALING`, `MO-CUTOFF-IDENTIFICATION`, `DEF-CUTOFF-TRACE-DEFECT`, `VA-CONSTANT-SHEAR-TRACE` |  |
| `MO-Q3-DERIVATIVE-MOMENTS` | Covariance moments of spatial derivatives | `MO-Q3-IDENTITIES` |  |
| `MO-Q3-IDENTITIES` | Normalization, covariance polynomial, derivative ratios | `DEF-Q3-KERNEL`, `DEF-Q3-COV` |  |
| `MO-SHELL-SCALING` | Independent shell law and geometric variance sum | `EXT-Algsuperdiff-Frozen-Assumptions-ShellLawPrefix-marginal-scaling`, `EXT-Algsuperdiff-Frozen-Assumptions-ShellLawPrefix-independent`, `DEF-SHELL-VARIANCE`, `DEF-PLANAR-Q3-GAUSSIAN`, `MO-Q3-IDENTITIES` |  |
| `MO-SPECTRAL` | First-chaos reduction of the frozen stationary projection | `DEF-PLANAR-Q3-GAUSSIAN`, `EXT-Algsuperdiff-Probability-Stationary-stationaryPotentialProjection`, `EXT-Algsuperdiff-Frozen-Assumptions-ShellField-zeroShellPotentialCorrector` | [`SpectralModel.lean`](../ASDExplicitGamma/Model/SpectralModel.lean) |
| `MO-SPECTRAL-ISOMETRY` | First-chaos spectral isometry | `MO-SPECTRAL`, `MO-Q3-IDENTITIES`, `DEF-Q3-COV` | [`SpectralFirstChaosIsometry.lean`](../ASDExplicitGamma/Model/SpectralFirstChaosIsometry.lean) |
| `MO-TRANSLATION` | Translation of cutoff observables to arbitrary cells | `EXT-Algsuperdiff-Section3-Cutoff-coefficientCutoffLaw-stationary-real`, `VA-MU-ADAPTER`, `MO-CUTOFF-IDENTIFICATION` | [`Translation.lean`](../ASDExplicitGamma/Model/Translation.lean) |

## Gaussian tools

| Step | Title | Uses | Lean |
|---|---|---|---|
| `GA-BACKWARD-HEAT` | Exact auxiliary backward-heat test | `GA-RESPONSE-ANALYTIC`, `GA-TWO-PARAM`, `GA-FIN-HEAT` |  |
| `GA-BORELL` | Sharp finite-dimensional Gaussian concentration | `GA-FIN-IBP` |  |
| `GA-C2-TEST` | General Gaussian C2-test lemma | `GA-FIN-HEAT`, `GA-FIXED-NU`, `GA-FINITE-RANK-PASSAGE`, `GA-COVARIANCE-TRACE` |  |
| `GA-CM-OPERATOR` | q3 covariance factor and mixed-derivative regularity | `MO-Q3-IDENTITIES` |  |
| `GA-CM-REALIZATION` | Cameron--Martin realization of the frozen shell law | `DEF-PLANAR-Q3-GAUSSIAN`, `GA-CM-OPERATOR`, `GA-CM-SERIES`, `EXT-Algsuperdiff-Frozen-Assumptions-ShellLawPrefix-marginal-scaling`, `EXT-Matrix-IsHermitian-spectral-theorem` |  |
| `GA-CM-SERIES` | Gaussian Hilbert series Lp convergence |  | [`SeriesMoment.lean`](../ASDExplicitGamma/Gaussian/SeriesMoment.lean) |
| `GA-COVARIANCE-TRACE` | Absolute covariance trace and basis independence | `GA-CM-SERIES`, `GA-OLDER-FIELD`, `GA-CM-REALIZATION`, `GA-RESPONSE-ANALYTIC` |  |
| `GA-DERIVATIVE-LAW` | Joint Gaussian law of the stored shell derivatives | `DEF-PLANAR-Q3-GAUSSIAN`, `EXT-Algsuperdiff-Frozen-Assumptions-ShellField`, `MO-Q3-IDENTITIES`, `MO-SHELL-SCALING` |  |
| `GA-FIN-HEAT` | Finite-rank covariance heat identity | `GA-FIN-IBP` | [`SeriesHeat.lean`](../ASDExplicitGamma/Gaussian/SeriesHeat.lean) |
| `GA-FIN-IBP` | Finite-dimensional Gaussian integration by parts | `EXT-ProbabilityTheory-gaussianReal` |  |
| `GA-FINITE-RANK-PASSAGE` | Uniform rank limit for the heat identity | `GA-CM-SERIES`, `GA-CM-REALIZATION`, `GA-RESPONSE-ANALYTIC`, `GA-FIXED-NU`, `GA-COVARIANCE-TRACE`, `GA-OLDER-FIELD` | [`SeriesPassage.lean`](../ASDExplicitGamma/Gaussian/SeriesPassage.lean) |
| `GA-FIXED-NU` | Fixed-viscosity response, trace and inverse-history bounds | `GA-HEAT-SPACE`, `VA-COARSE-DUALITY` |  |
| `GA-GENERATOR-BOUNDS` | Producing generator and bracket inequalities | `VA-NILPOTENT-SHEAR`, `VA-LOCALIZED-SHEAR`, `VA-PROJECTED-SOURCE`, `VA-FORCED-SOURCE`, `TR-INTERPOLANT-ESTIMATES`, `TR-PRODUCT`, `TR-POINCARE-CELL-CONSTANTS`, `NU-AO-CIR-GATES`, `VA-LEMMA-V`, `VA-LEMMA-V-H2-BAND`, `GA-CM-REALIZATION`, `NU-GA-MU-STAR` |  |
| `GA-GENERATOR-SPLIT` | Exact center, mixed, and remainder split | `VA-CONSTANT-SKEW`, `GA-RESPONSE-ANALYTIC`, `GA-CM-REALIZATION`, `GA-COVARIANCE-TRACE`, `GA-BACKWARD-HEAT` |  |
| `GA-HEAT` | True-law q3 insertion heat identity | `GA-HEAT-SPACE`, `GA-FIXED-NU`, `GA-CM-REALIZATION`, `GA-OLDER-FIELD`, `GA-COVARIANCE-TRACE`, `GA-FINITE-RANK-PASSAGE`, `GA-C2-TEST`, `GA-FIN-HEAT`, `MO-CUTOFF-IDENTIFICATION` | [`ModelHeatTrace.lean`](../ASDExplicitGamma/Gaussian/ModelHeatTrace.lean) |
| `GA-HEAT-SPACE` | Closed response space and unique minimum |  |  |
| `GA-MISSING-WAVE` | Missing-wave moments | `MO-SHELL-SCALING`, `MO-Q3-IDENTITIES`, `DEF-NATIVE-STATE` |  |
| `GA-MOMENT-CHAIN` | Gaussian power chain rule | `GA-C2-TEST`, `GA-COVARIANCE-TRACE`, `GA-HEAT` | [`SeriesPower.lean`](../ASDExplicitGamma/Gaussian/SeriesPower.lean) |
| `GA-OLDER-FIELD` | Convergence and moments of the completed older field | `MO-SHELL-SCALING`, `GA-CM-REALIZATION`, `GA-CM-SERIES` | [`OlderField.lean`](../ASDExplicitGamma/Gaussian/OlderField.lean) |
| `GA-P12` | Regularized moment transport and all-real-order inequality | `GA-GENERATOR-BOUNDS`, `GA-C2-TEST`, `TR-INV-HISTORY`, `GA-HEAT` |  |
| `GA-REMAINDER-HEAT` | Centered-remainder covariance heat identity | `GA-CM-REALIZATION`, `GA-CM-SERIES`, `GA-COVARIANCE-TRACE`, `GA-FIN-HEAT`, `GA-FINITE-RANK-PASSAGE`, `GA-C2-TEST` |  |
| `GA-RESPONSE-ANALYTIC` | Analytic response dependence on the coefficient | `GA-HEAT-SPACE`, `GA-FIXED-NU`, `VA-NILPOTENT-SHEAR` | [`Analytic.lean`](../ASDExplicitGamma/Response/Analytic.lean) |
| `GA-RIO` | Rio martingale type-two inequality | `GA-RIO-LP-CONVEXITY` |  |
| `GA-RIO-LP-CONVEXITY` | One-step L^p smoothness inequality |  |  |
| `GA-SUP-MEAN` | Gaussian tensor-supremum mean and Lipschitz bounds | `DEF-WAVE-GATE-CONSTANTS`, `GA-DERIVATIVE-LAW`, `GA-BORELL` |  |
| `GA-TWO-PARAM` | Time-dependent Gaussian heat identity | `GA-FIN-HEAT`, `GA-CM-SERIES`, `GA-FINITE-RANK-PASSAGE`, `GA-OLDER-FIELD`, `GA-CM-REALIZATION`, `GA-COVARIANCE-TRACE` |  |
| `GA-WAVE-GATE` | Planar Gaussian derivative tail gate | `GA-DERIVATIVE-LAW`, `GA-SUP-MEAN`, `GA-BORELL`, `DEF-NATIVE-STATE`, `DEF-WAVE-GATE-CONSTANTS` |  |
| `GA-WHOLE-ROOT` | Gaussian spatial moment estimate | `GA-CM-REALIZATION`, `MO-SHELL-SCALING`, `MO-Q3-IDENTITIES`, `GA-BORELL`, `DEF-NATIVE-STATE` |  |

## Variational toolkit

| Step | Title | Uses | Lean |
|---|---|---|---|
| `VA-ADJOINT-REDUNDANCY` | Coarse adjoint block identity | `VA-MU-ADAPTER`, `EXT-Homogenization-blockMatrixOfCoeff-matTranspose`, `EXT-Homogenization-coarseBlockMatrix-adjointCoeffField-of-exists` |  |
| `VA-COARSE-DUALITY` | Coarse inverse duality and nonnegative trace defect | `VA-MU-ADAPTER`, `EXT-Homogenization-coarseBlockMatrix` |  |
| `VA-COLD-GRAPH` | Cold parent-from-children graph inequality | `VA-COARSE-DUALITY`, `VA-SUBADDITIVITY`, `VA-TRUE-FRAME-MEAN`, `VA-ADJOINT-REDUNDANCY` |  |
| `VA-COMPATIBLE-COERCIVITY` | Compatible and paired coercivity | `VA-ENERGYMAP`, `TR-INV-HISTORY`, `VA-COARSE-DUALITY`, `VA-SUBADDITIVITY` |  |
| `VA-CONSTANT-SHEAR-TRACE` | Constant-shear trace formula and vanishing derivative | `VA-CONSTANT-SKEW`, `VA-COARSE-DUALITY`, `VA-MU-ADAPTER` |  |
| `VA-CONSTANT-SKEW` | Constant-skew gauge invariance | `VA-NILPOTENT-SHEAR`, `VA-MU-ADAPTER`, `EXT-Homogenization-coarseBlockMatrix` |  |
| `VA-DEFECT` | Lemma V defect decomposition | `VA-RESP-IDENTITIES`, `VA-MU-ADAPTER`, `VA-COARSE-DUALITY`, `DEF-TRACE-DEFECT` |  |
| `VA-DUAL-IDENTITY` | Source-defined starred inverse identity | `EXT-Homogenization-coarseStarredBlockMatrixInv-eq-blockReflect` |  |
| `VA-ENERGYMAP` | Nonsymmetric energy-to-gradient estimate with coarse-data bridge | `EXT-Homogenization-Book-Ch02-vecNormSq-averageGradient-le-matrixNorm-sigmaStarInvCoa`, `VA-ENERGYMAP-DATA`, `EXT-Homogenization-Internal-Ch02-BookCh02-book-coarseBlockMatrix-eq-old-coarseBlockM`, `VA-MU-ADAPTER` | [`EnergyMap.lean`](../ASDExplicitGamma/Variational/EnergyMap.lean) |
| `VA-ENERGYMAP-DATA` | Producer for Book.Ch02 coarse data | `EXT-Homogenization-Internal-Ch02-BookCh02-exists-oldCanonicalMatrixData-of-isOpenBou`, `EXT-Homogenization-sigmaStarInvCoarse-posDef-of-isEllipticFieldOn-of-isOpenBoundedCo`, `EXT-Homogenization-isUnit-det-of-isSigmaStarCoarse-of-isEllipticFieldOn-of-isOpenBou` | [`EnergyMap.lean`](../ASDExplicitGamma/Variational/EnergyMap.lean) |
| `VA-ENVELOPE` | Coefficient first variation | `VA-NILPOTENT-SHEAR`, `EXT-Homogenization-MuHilbertRealization-minimizerMap-firstVariation`, `EXT-Algsuperdiff-Frozen-Section24-existsUnique-coarseMatrixDerivative`, `VA-MU-ADAPTER`, `GA-HEAT-SPACE` |  |
| `VA-FORCED-SOURCE` | Forced-source feedback | `VA-COMPATIBLE-COERCIVITY`, `VA-PROJECTED-SOURCE`, `TR-PAIRED-BESSEL` |  |
| `VA-INTERPOLANT-ESTIMATES` | Coercive-data adapter for interpolant estimates | `TR-INTERPOLANT-ESTIMATES`, `TR-DIAG-INTERPOLANT`, `TR-BROKEN-NORMS` |  |
| `VA-INTERPOLANT-LIFT` | Exact skew lift identity | `VA-LOCALIZED-SHEAR`, `TR-DIAG-INTERPOLANT` |  |
| `VA-LEMMA-V` | Vanishing trace bracket | `VA-DEFECT`, `VA-ENVELOPE`, `VA-INTERPOLANT-LIFT`, `TR-KP-RIESZ`, `VA-LEMMA-V-H1`, `TR-BROKEN-NORMS` |  |
| `VA-LEMMA-V-H1` | Harmonic weak-gradient bound | `VA-ENERGYMAP`, `TR-INV-HISTORY`, `TR-HISTORY-MONOTONE`, `VA-SUBADDITIVITY`, `VA-ADJOINT-REDUNDANCY`, `VA-OPEN-CUBE-ADAPTER` |  |
| `VA-LEMMA-V-H2-BAND` | Stationary-band row-form estimate | `TR-PRODUCT`, `TR-DIAG-INTERPOLANT`, `TR-BROKEN-NORMS`, `VA-INTERPOLANT-ESTIMATES` |  |
| `VA-LEMMA-V-H2-REMAINDER` | Nonstationary remainder row-form estimate | `GA-DERIVATIVE-LAW`, `TR-PRODUCT`, `TR-DIAG-INTERPOLANT`, `TR-BROKEN-NORMS`, `VA-INTERPOLANT-ESTIMATES`, `MO-Q3-DERIVATIVE-MOMENTS` |  |
| `VA-LEMMA-V-H2-SINGLE` | Single-direction constant-shear estimate | `TR-PRODUCT`, `TR-DIAG-INTERPOLANT`, `TR-BROKEN-NORMS`, `VA-INTERPOLANT-ESTIMATES`, `MO-Q3-DERIVATIVE-MOMENTS` |  |
| `VA-LOCALIZED-SHEAR` | Weak localized shear and admissible-space automorphism | `VA-MU-ADAPTER`, `TR-DIAG-INTERPOLANT` |  |
| `VA-MU-ADAPTER` | CoarseGraining response equals the energy matrix | `EXT-Homogenization-mu-eq-half-coarseBlockMatrix-cube`, `EXT-Homogenization-coarseBlockMatrix`, `EXT-Homogenization-coarseBlockMatrix-translateSet-eq-translateCoeffField`, `EXT-Homogenization-isCoarseBlockMatrix-translateSet-iff`, `MO-COARSE-CONGRUENCE`, `DEF-TRACE-DEFECT`, `GA-HEAT-SPACE` |  |
| `VA-NILPOTENT-SHEAR` | Second variation and trial inequality |  | [`NilpotentShear.lean`](../ASDExplicitGamma/Response/NilpotentShear.lean) |
| `VA-OPEN-CUBE-ADAPTER` | Half-open statement cube to open source cube | `VA-MU-ADAPTER`, `EXT-Homogenization-cubeSet`, `EXT-Homogenization-openCubeSet` |  |
| `VA-PROJECTED-SOURCE` | Pure projected-source energy | `VA-COMPATIBLE-COERCIVITY`, `TR-KP-RIESZ`, `TR-INV-HISTORY` |  |
| `VA-RESP-IDENTITIES` | Response quadratic identities on source cubes | `VA-MU-ADAPTER`, `VA-OPEN-CUBE-ADAPTER` |  |
| `VA-SUBADDITIVITY` | Response and block-matrix subadditivity | `EXT-Homogenization-responseJ-subadditive-openCubeSet-childCubes-of-isEllipticFieldOn`, `EXT-Homogenization-coarseBlockMatrix-subadditive-openCubeSet-descendantsAtDepth-in-l`, `VA-RESP-IDENTITIES`, `VA-OPEN-CUBE-ADAPTER` |  |
| `VA-TRUE-FRAME-MEAN` | Annealed response in the true homogenized frame | `MO-TRANSLATION`, `EXT-Algsuperdiff-Section3-Provider-Annealed-coefficientCutoffLaw-exists-annealedBloc`, `EXT-Algsuperdiff-Section3-Provider-Diffusivity-ApproximateRecurrence-blockMatLoewner`, `VA-MU-ADAPTER` | [`TrueFrame.lean`](../ASDExplicitGamma/Variational/TrueFrame.lean) |

## Triadic cubes, transport and sensitivity

| Step | Title | Uses | Lean |
|---|---|---|---|
| `TR-BROKEN-NORMS` | Broken triadic weak and positive norms | `TR-KP-RIESZ` |  |
| `TR-COARSE-SENSITIVITY-DERIVATIVE` | Explicit first variation and derivative bounds | `VA-ENVELOPE`, `EXT-Algsuperdiff-Frozen-Section24-existsUnique-coarseMatrixDerivative`, `TR-POINCARE-CELL-CONSTANTS`, `TR-PRODUCT`, `TR-KP-RIESZ`, `TR-SENSITIVITY-RESTRICTION`, `VA-ADJOINT-REDUNDANCY`, `VA-CONSTANT-SKEW` |  |
| `TR-COARSE-SENSITIVITY-ODE` | Integrate the coarse sensitivity inequalities | `TR-COARSE-SENSITIVITY-DERIVATIVE`, `TR-SENSITIVITY-RESTRICTION`, `VA-CONSTANT-SKEW` |  |
| `TR-DIAG-INTERPOLANT` | DIAG nodal-average interpolant |  |  |
| `TR-HISTORY-MONOTONE` | Raw and normalized quarter histories from nondecreasing maxima |  |  |
| `TR-INTERPOLANT-ESTIMATES` | Quantitative DIAG interpolant bounds | `TR-DIAG-INTERPOLANT`, `TR-BROKEN-NORMS`, `TR-POINCARE-CELL-CONSTANTS`, `TR-PRODUCT`, `TR-KP-RIESZ` |  |
| `TR-INV-HISTORY` | Complete inverse history | `EXT-Homogenization-coarseBlockMatrix` |  |
| `TR-KP-RIESZ` | Weak/positive norms, duality, and Bessel | `EXT-ASDExplicitGamma-Triadic-abs-pairing-le-dual-primal-of-pairing-limit`, `EXT-InnerProductSpace-toDual`, `EXT-ASDExplicitGamma-Triadic-Torus-tsum-sq-boxCoeff-le` |  |
| `TR-PAIRED-BESSEL` | Paired Bessel budget for homogeneous fields | `TR-KP-RIESZ`, `VA-COARSE-DUALITY`, `VA-ENERGYMAP` |  |
| `TR-POINCARE-CELL-CONSTANTS` | Sharp cube and triadic Poincaré constants | `TR-SENSITIVITY-TAIL` |  |
| `TR-POINCARE-SENSITIVITY` | Poincaré, product, interpolant, and explicit coarse-sensitivity package | `TR-POINCARE-CELL-CONSTANTS`, `TR-PRODUCT`, `TR-INTERPOLANT-ESTIMATES`, `TR-COARSE-SENSITIVITY-DERIVATIVE`, `TR-COARSE-SENSITIVITY-ODE` |  |
| `TR-PRODUCT` | Exact triadic positive-norm product inequality | `TR-POINCARE-CELL-CONSTANTS`, `TR-SENSITIVITY-TAIL` |  |
| `TR-SENSITIVITY-RESTRICTION` | Exact all-cell weak-norm restriction inequality | `TR-KP-RIESZ` |  |
| `TR-SENSITIVITY-TAIL` | Positive-norm tail identity | `TR-KP-RIESZ` |  |

## Cold start and cold observation

| Step | Title | Uses | Lean |
|---|---|---|---|
| `CO-COLD-FIVE-SIXTHS-CANDIDATE` | Five-sixths graph candidate | `CO-COLD-LAG-INTERPOLATION`, `CO-SPECTRAL-PAIR`, `MO-FOUR-COLOR`, `SC-TRUE-FRAME-NORMALIZATION` |  |
| `CO-COLD-HISTORY-CAPS` | Depthwise history and monotone maxima | `CO-COLD-MOMENT-CAPS`, `DEF-NATIVE-STATE`, `VA-SUBADDITIVITY`, `MO-TRANSLATION` |  |
| `CO-COLD-LAG-INTERPOLATION` | L1/L20 lag interpolation | `CO-COLD-MOMENT-CAPS`, `NU-CO-ROOT2` | [`Interpolation.lean`](../ASDExplicitGamma/Cold/Interpolation.lean) |
| `CO-COLD-MOMENT-CAPS` | Cold moment caps and exact centering | `GA-RIO`, `MO-LOCAL-INDEPENDENCE`, `MO-FOUR-COLOR`, `SC-TRUE-FRAME-NORMALIZATION`, `DEF-NATIVE-STATE`, `CO-EXACT-CENTERING`, `VA-COARSE-DUALITY` |  |
| `CO-COLD-OLD-GRAPH-CAP` | Old-graph candidate | `CO-COLD-LAG-INTERPOLATION`, `CO-SPECTRAL-PAIR`, `SC-TRUE-FRAME-NORMALIZATION`, `VA-SUBADDITIVITY` |  |
| `CO-EXACT-CENTERING` | Exact centering for nonnegative variables |  | [`ExactCentering.lean`](../ASDExplicitGamma/Cold/ExactCentering.lean) |
| `CO-EXPECTED-BLOCK-SYMMETRY` | Expected response block form | `VA-TRUE-FRAME-MEAN`, `MO-TRANSLATION`, `SC-TRUE-FRAME-NORMALIZATION` | [`BlockSymmetry.lean`](../ASDExplicitGamma/Cold/BlockSymmetry.lean) |
| `CO-GRAPH-SANDWICH` | In-grid parent graph candidate | `VA-COLD-GRAPH`, `VA-COARSE-DUALITY`, `SC-TRUE-FRAME-NORMALIZATION`, `CO-EXPECTED-BLOCK-SYMMETRY`, `VA-SUBADDITIVITY`, `MO-FOUR-COLOR`, `CO-COLD-LAG-INTERPOLATION` |  |
| `CO-PLATEAU-NEUMANN-SQUARE` | Square Neumann Hessian identity |  |  |
| `CO-PLATEAU-P1` | Cutoff moments |  |  |
| `CO-PLATEAU-P2` | Transport weights | `CO-PLATEAU-P1`, `CO-PLATEAU-NEUMANN-SQUARE`, `CO-PLATEAU-STREAM-FUNCTION`, `TR-POINCARE-CELL-CONSTANTS`, `NU-CO-PLATEAU-PI`, `VA-SUBADDITIVITY`, `CO-PLATEAU-RESIDUAL-POINCARE` |  |
| `CO-PLATEAU-P3` | Gram estimate | `VA-COARSE-DUALITY`, `SC-TRUE-FRAME-NORMALIZATION`, `VA-SUBADDITIVITY` |  |
| `CO-PLATEAU-P4` | Cutoff recovery | `CO-PLATEAU-P1`, `NU-CO-PLATEAU-PI`, `VA-SUBADDITIVITY`, `MO-TRANSLATION` |  |
| `CO-PLATEAU-P5` | Good/bad projection split | `CO-PLATEAU-P3`, `SC-TRUE-FRAME-NORMALIZATION`, `VA-SUBADDITIVITY` |  |
| `CO-PLATEAU-P6` | Fine tail | `CO-PLATEAU-P3`, `NU-CO-PLATEAU-TAIL` |  |
| `CO-PLATEAU-RECURRENCE` | Reconstructed plateau inequality | `CO-PLATEAU-P1`, `CO-PLATEAU-P2`, `CO-PLATEAU-P3`, `CO-PLATEAU-P4`, `CO-PLATEAU-P5`, `CO-PLATEAU-P6`, `NU-CO-PLATEAU-PI`, `NU-CO-PLATEAU-TAIL` |  |
| `CO-PLATEAU-RESIDUAL-POINCARE` | Residual Poincare constant on the square |  |  |
| `CO-PLATEAU-STREAM-FUNCTION` | Square stream function |  |  |
| `CO-SPECTRAL-PAIR` | Centered spectral pair estimate | `VA-COARSE-DUALITY`, `SC-TRUE-FRAME-NORMALIZATION` |  |
| `CO-THETA-SCALING` | Proportional cold continuation | `CO-TRIANGULAR-129`, `NU-CO-ROOT2`, `NU-CO-COLD-LAGS` |  |
| `CO-TRIANGULAR-129` | Same-law cold recurrence through lag 128 | `CO-COLD-MOMENT-CAPS`, `CO-COLD-HISTORY-CAPS`, `CO-COLD-LAG-INTERPOLATION`, `CO-COLD-OLD-GRAPH-CAP`, `CO-COLD-FIVE-SIXTHS-CANDIDATE`, `CO-GRAPH-SANDWICH`, `CO-PLATEAU-RECURRENCE`, `SC-TRUE-FRAME-NORMALIZATION`, `VA-COARSE-DUALITY`, `VA-SUBADDITIVITY`, `MO-FOUR-COLOR`, `DEF-NATIVE-STATE` |  |

## Scalar corridor

| Step | Title | Uses | Lean |
|---|---|---|---|
| `SC-ANALYTIC-BOUND-M` | Operator bound from coarse duality | `VA-COARSE-DUALITY`, `SC-TRUE-FRAME-NORMALIZATION` |  |
| `SC-CHAOS-MOMENT-BOUND` | Fourth-chaos moment comparison | `GA-CM-REALIZATION`, `NU-SC-LOWER-FACTORS` | [`ChaosDefectEnvelope.lean`](../ASDExplicitGamma/Scalar/ChaosDefectEnvelope.lean), [`ChaosMultiShellTransfer.lean`](../ASDExplicitGamma/Scalar/ChaosMultiShellTransfer.lean) |
| `SC-COLD-RECIPROCAL-NORMALIZATION` | Cold trace to reciprocal normalization | `DEF-NATIVE-STATE`, `SC-TRUE-FRAME-NORMALIZATION`, `CO-EXPECTED-BLOCK-SYMMETRY`, `CO-TRIANGULAR-129`, `NU-CO-COLD-LAGS` |  |
| `SC-DEFECT-ENERGY-BOUND` | Defect source energy | `VA-PROJECTED-SOURCE`, `GA-CM-REALIZATION` |  |
| `SC-DIRICHLET-SQUARE-HESSIAN` | Square Dirichlet Hessian identity |  |  |
| `SC-ENTRANCE-MOLECULAR-STARTUP` | Five-coordinate native startup | `SC-MOLECULAR-LOWER`, `SC-MOLECULAR-UPPER`, `NA-MOLECULAR-BOX`, `DEF-NATIVE-STATE`, `DEF-SHELL-VARIANCE` |  |
| `SC-EXACT-LAW-SCALING` | Exact self-similar scalar law | `MO-AMPLITUDE-INVARIANCE`, `MO-SHELL-SCALING`, `EXT-Algsuperdiff-Section3-Annealed-sigmaBar`, `EXT-Algsuperdiff-Section3-Annealed-sigmaBar-characterization` |  |
| `SC-LONGBLOCK-NO-LOSS` | Long-block no-loss limit | `VA-CONSTANT-SKEW`, `VA-SUBADDITIVITY`, `MO-FOUR-COLOR`, `TR-INV-HISTORY`, `MO-SHELL-SCALING`, `EXT-Algsuperdiff-Section3-Annealed-sigmaBar`, `EXT-Algsuperdiff-Section3-Annealed-sigmaBar-characterization` |  |
| `SC-GAUSSIAN-PRODUCT-BOUND` | Gaussian product moment |  |  |
| `SC-LAMBDA3-RESIDUE` | Joint-disk and two-potential residue | `TR-PAIRED-BESSEL` |  |
| `SC-LAMBDA8-DUALITY-STEP` | Global convex-duality admissibility | `VA-COARSE-DUALITY`, `SC-TRUE-FRAME-NORMALIZATION`, `VA-DUAL-IDENTITY` |  |
| `SC-LAMBDA8-LOAD-INPUTS` | One-load load and oscillation inputs | `VA-PROJECTED-SOURCE`, `TR-POINCARE-SENSITIVITY`, `TR-INTERPOLANT-ESTIMATES`, `NU-SC-LOWER-COERCIVITY` |  |
| `SC-LAMBDA8-TOP-SOURCE-RESIDUAL` | Top-source residual | `TR-INV-HISTORY`, `VA-TRUE-FRAME-MEAN` |  |
| `SC-LONGBLOCK-TRIAL` | Long-block upper scalar implication | `SC-UPPER-CELL-ENERGY`, `SC-LONGBLOCK-NO-LOSS`, `SC-SOURCE-ENDPOINT-COROLLARY`, `SC-UPPER-ENDPOINT-DOMINATION`, `SC-UPPER-SOURCE-CAPS` | [`UpperLongblockTrial.lean`](../ASDExplicitGamma/Scalar/UpperLongblockTrial.lean) |
| `SC-LOWER-CORRIDOR` | Target-label lower scalar implication | `SC-ONE-SHELL-RECIPROCAL-DROP`, `SC-RECIPROCAL-TELESCOPE`, `SC-MOLECULAR-LOWER`, `SC-TRUE-FRAME-NORMALIZATION`, `SC-COLD-RECIPROCAL-NORMALIZATION`, `SC-RECIPROCAL-MOLECULAR-CAP`, `SC-STRUCTURAL-CONTINUITY`, `CO-TRIANGULAR-129`, `MO-SHELL-SCALING`, `NU-SC-K-MARGIN`, `NU-SC-CLOCKS`, `NU-CO-COLD-LAGS`, `DEF-NATIVE-STATE` | [`LowerCorridorGen.lean`](../ASDExplicitGamma/Scalar/LowerCorridorGen.lean) |
| `SC-LOWER-INPUT-BRIDGE` | Old-law source and mixed-bridge interface | `NA-SOURCE-ROWS`, `NA-Q1-BOUNDARY-CHARGE`, `IN-RESET-INPUTS`, `IN-GLOBAL-INVERSE-BANK`, `IN-LOCAL-INVERSE-BANK`, `IN-MIXED-BRIDGE`, `NU-SC-OLD-GROUPED-REMAINDER`, `NU-SC-BRIDGE-RESERVE`, `SC-SOURCE-ENDPOINT-COROLLARY`, `DEF-NATIVE-STATE` | [`LowerChainInput.lean`](../ASDExplicitGamma/Scalar/LowerChainInput.lean) |
| `SC-MOLECULAR-FIVE-FOUR` | Molecular \(5/4\) estimate | `SC-MOLECULAR-UPPER`, `NU-SC-UPPER-STARTUP` |  |
| `SC-MOLECULAR-LOWER` | Constant molecular competitor | `DEF-PLANAR-Q3-GAUSSIAN`, `EXT-Algsuperdiff-Section3-Annealed-sigmaBar-characterization`, `EXT-Algsuperdiff-Section3-Annealed-sigmaBar` | [`Molecular.lean`](../ASDExplicitGamma/Scalar/Molecular.lean) |
| `SC-MOLECULAR-UPPER` | Projected molecular upper bound | `EXT-Algsuperdiff-Section3-Annealed-sigmaBar-characterization`, `VA-ENERGYMAP`, `MO-J4-CSTAR`, `DEF-SHELL-VARIANCE`, `EXT-Algsuperdiff-Section3-Annealed-sigmaBar` |  |
| `SC-NEW-RESOLVENT-COMBINE` | Quartic combination and C-sharp bound | `SC-NEW-RESOLVENT-FLAT`, `SC-NEW-RESOLVENT-DEFECT`, `NU-SC-FRAME-FACTOR` | [`CombineFinal.lean`](../ASDExplicitGamma/Scalar/CombineFinal.lean) |
| `SC-NEW-RESOLVENT-DEFECT` | Defect fourth-moment contribution | `SC-RESOLVENT-IDENTITY`, `SC-DIRICHLET-SQUARE-HESSIAN`, `SC-SMOOTH-FEEDBACK-GAP`, `SC-LAMBDA8-LOAD-INPUTS`, `SC-GAUSSIAN-PRODUCT-BOUND`, `SC-CHAOS-MOMENT-BOUND`, `SC-DEFECT-ENERGY-BOUND`, `SC-LOWER-INPUT-BRIDGE`, `TR-PAIRED-BESSEL`, `VA-TRUE-FRAME-MEAN`, `TR-INTERPOLANT-ESTIMATES`, `TR-PRODUCT`, `IN-GLOBAL-INVERSE-BANK`, `IN-LOCAL-INVERSE-BANK`, `IN-MIXED-BRIDGE`, `NU-SC-LOWER-COERCIVITY`, `NU-SC-LOWER-FACTORS` | [`RefNodeRR.lean`](../ASDExplicitGamma/Scalar/RefNodeRR.lean) |
| `SC-NEW-RESOLVENT-FLAT` | Flat fourth-moment contribution | `SC-RESOLVENT-IDENTITY`, `SC-GAUSSIAN-PRODUCT-BOUND`, `SC-CHAOS-MOMENT-BOUND`, `SC-DIRICHLET-SQUARE-HESSIAN`, `TR-INTERPOLANT-ESTIMATES`, `TR-PRODUCT`, `IN-GLOBAL-INVERSE-BANK`, `NU-SC-LOWER-FACTORS` |  |
| `SC-NU-MONOTONICITY` | Fixed-law viscosity comparison | `VA-ENERGYMAP` |  |
| `SC-OLD-HESSIAN-TRIAL` | Ten-term OLD-Hessian generator bound | `SC-RESOLVENT-IDENTITY`, `SC-RESOLVENT-PARITY`, `VA-COMPATIBLE-COERCIVITY`, `VA-PROJECTED-SOURCE`, `VA-FORCED-SOURCE`, `TR-PAIRED-BESSEL`, `SC-LAMBDA3-RESIDUE`, `SC-DIRICHLET-SQUARE-HESSIAN`, `SC-ANALYTIC-BOUND-M`, `GA-CM-REALIZATION`, `GA-FINITE-RANK-PASSAGE`, `TR-POINCARE-SENSITIVITY`, `TR-INTERPOLANT-ESTIMATES`, `TR-PRODUCT`, `VA-INTERPOLANT-LIFT`, `MO-FOUR-COLOR`, `TR-INV-HISTORY`, `SC-LOWER-INPUT-BRIDGE`, `SC-SOURCE-ENDPOINT-COROLLARY`, `NU-SC-OLD-GROUPED-REMAINDER`, `NU-SC-H-SOURCE`, `NU-SC-BFLAT-MONOTONE-TAIL`, `NU-SC-LOWER-COERCIVITY`, `NU-SC-LOWER-FACTORS`, `DEF-NATIVE-STATE` | [`OldHessianTrialFinal.lean`](../ASDExplicitGamma/Scalar/OldHessianTrialFinal.lean) |
| `SC-ONE-SHELL-RECIPROCAL-DROP` | Old-law generator to reciprocal drop | `SC-RESOLVENT-IDENTITY`, `SC-RESOLVENT-PARITY`, `SC-OLD-HESSIAN-TRIAL`, `SC-NEW-RESOLVENT-COMBINE`, `SC-TRUE-FRAME-NORMALIZATION`, `NU-SC-K-MARGIN`, `NU-SC-LOG3-UPPER`, `DEF-NATIVE-STATE` | [`DropOneShellGen.lean`](../ASDExplicitGamma/Scalar/DropOneShellGen.lean) |
| `SC-RECIPROCAL-MOLECULAR-CAP` | Constant-flux entrance bound | `VA-ENERGYMAP`, `EXT-Algsuperdiff-Section3-Annealed-sigmaBar-characterization` |  |
| `SC-RECIPROCAL-TELESCOPE` | Two-region reciprocal conversion |  |  |
| `SC-RESOLVENT-IDENTITY` | Exact finite-amplitude response identity | `VA-NILPOTENT-SHEAR`, `GA-CM-REALIZATION`, `GA-FINITE-RANK-PASSAGE` | [`PhysicalResolventIdentity.lean`](../ASDExplicitGamma/Scalar/PhysicalResolventIdentity.lean) |
| `SC-RESOLVENT-PARITY` | Even-order parity cancellation | `SC-RESOLVENT-IDENTITY`, `GA-CM-REALIZATION`, `GA-FINITE-RANK-PASSAGE`, `GA-GENERATOR-SPLIT`, `NA-FINITE-PROFILE` | [`PhysicalResolventParity.lean`](../ASDExplicitGamma/Scalar/PhysicalResolventParity.lean), [`ResolventParityHilbert.lean`](../ASDExplicitGamma/Scalar/ResolventParityHilbert.lean) |
| `SC-SMOOTH-FEEDBACK-GAP` | Smooth-feedback estimate \(\Lambda_8\) | `SC-LAMBDA8-DUALITY-STEP`, `SC-LAMBDA8-TOP-SOURCE-RESIDUAL`, `SC-LAMBDA8-LOAD-INPUTS`, `SC-ANALYTIC-BOUND-M`, `NU-SC-H-SOURCE`, `SC-TRUE-FRAME-NORMALIZATION`, `VA-COARSE-DUALITY`, `VA-SUBADDITIVITY`, `VA-COMPATIBLE-COERCIVITY`, `VA-PROJECTED-SOURCE`, `VA-FORCED-SOURCE`, `VA-ADJOINT-REDUNDANCY`, `VA-TRUE-FRAME-MEAN`, `TR-PAIRED-BESSEL`, `TR-INV-HISTORY`, `TR-KP-RIESZ`, `MO-TRANSLATION`, `MO-LOCAL-INDEPENDENCE`, `MO-PRODUCT-Q3-D4-GAUGE`, `DEF-CUTOFF-TRACE-DEFECT`, `IN-MIXED-BRIDGE`, `GA-CM-REALIZATION`, `GA-FINITE-RANK-PASSAGE` | [`SmoothFeedbackNode.lean`](../ASDExplicitGamma/Scalar/SmoothFeedbackNode.lean) |
| `SC-SOURCE-ENDPOINT-COROLLARY` | Endpoint source caps from the Part C owner | `NA-SOURCE-SMALLER-GAMMA` | [`SourceChainEndpoint.lean`](../ASDExplicitGamma/Native/SourceChainEndpoint.lean) |
| `SC-STRUCTURAL-CONTINUITY` | Exact scalar continuity | `SC-NU-MONOTONICITY`, `SC-EXACT-LAW-SCALING` |  |
| `SC-TRUE-FRAME-NORMALIZATION` | Full-block true-frame lower bound | `VA-TRUE-FRAME-MEAN`, `EXT-Algsuperdiff-Section3-Annealed-sigmaBar`, `DEF-TRACE-DEFECT`, `DEF-PLANAR-Q3-GAUSSIAN`, `VA-ENERGYMAP` |  |
| `SC-UPPER-CELL-ENERGY` | UPPER cell estimate | `SC-UPPER-SOURCE-CAPS`, `SC-UPPER-DEPTH14-HISTORY`, `SC-ANALYTIC-BOUND-M`, `SC-TRUE-FRAME-NORMALIZATION`, `SC-STRUCTURAL-CONTINUITY`, `SC-UPPER-SIGNAL-INTERVAL`, `TR-POINCARE-SENSITIVITY`, `TR-COARSE-SENSITIVITY-ODE`, `GA-SUP-MEAN`, `MO-FOUR-COLOR`, `VA-CONSTANT-SKEW`, `VA-SUBADDITIVITY`, `TR-INV-HISTORY`, `IN-RESET-INPUTS`, `IN-GLOBAL-INVERSE-BANK`, `IN-LOCAL-INVERSE-BANK`, `IN-FULL-RESPONSE-BANK`, `NU-IN-FULL-PROFILES`, `NU-SC-UPPER-ROW`, `NU-SC-UPPER-GEOMETRY`, `NU-SC-UPPER-ERROR`, `NU-SC-UPPER-SIGNAL-ARITH`, `DEF-NATIVE-STATE` | [`UpperCellEnergyFinal.lean`](../ASDExplicitGamma/Scalar/UpperCellEnergyFinal.lean) |
| `SC-UPPER-DEPTH14-HISTORY` | Depth-14 history from buffer 40 | `DEF-NATIVE-STATE`, `TR-INV-HISTORY`, `VA-SUBADDITIVITY`, `MO-TRANSLATION` |  |
| `SC-UPPER-ENDPOINT-DOMINATION` | Smaller-\(\gamma\) upper source domination | `SC-SOURCE-ENDPOINT-COROLLARY`, `SC-UPPER-SOURCE-CAPS`, `NU-SC-UPPER-ERROR`, `SC-UPPER-DEPTH14-HISTORY`, `IN-RESET-INPUTS`, `IN-FULL-RESPONSE-BANK` |  |
| `SC-UPPER-SIGNAL-INTERVAL` | Analytic signal interval from the earlier label | `SC-MOLECULAR-UPPER`, `DEF-NATIVE-STATE`, `NU-SC-UPPER-SIGNAL-ARITH` |  |
| `SC-UPPER-SOURCE-CAPS` | Long-block source cap interface | `IN-FULL-RESPONSE-BANK`, `NU-IN-FULL-PROFILES`, `SC-UPPER-T0-QUADRATURE`, `NU-SC-UPPER-T0-REPLAY`, `SC-UPPER-DEPTH14-HISTORY`, `SC-SOURCE-ENDPOINT-COROLLARY`, `IN-RESET-INPUTS`, `IN-GLOBAL-INVERSE-BANK`, `IN-LOCAL-INVERSE-BANK`, `NA-SOURCE-ROWS`, `DEF-NATIVE-STATE`, `MO-FOUR-COLOR`, `TR-INV-HISTORY` | [`UpperSourceCaps.lean`](../ASDExplicitGamma/Scalar/UpperSourceCaps.lean) |
| `SC-UPPER-STEP` | Target-label upper corridor | `SC-LONGBLOCK-TRIAL`, `SC-UPPER-SIGNAL-INTERVAL`, `SC-MOLECULAR-FIVE-FOUR`, `SC-MOLECULAR-UPPER`, `NU-SC-UPPER-ERROR`, `NU-SC-UPPER-BARRIER`, `DEF-NATIVE-STATE` |  |
| `SC-UPPER-T0-QUADRATURE` | Monotone parent-prefix quadrature |  |  |
| `SC-WEAK-CORRIDORS` | Weaker scalar corridors | `SC-MOLECULAR-LOWER`, `DEF-NATIVE-STATE` |  |

## Inverse estimates

| Step | Title | Uses | Lean |
|---|---|---|---|
| `IN-ANCHOR-ADAPTER` | Source coefficient and response identification | `MO-CUTOFF-IDENTIFICATION`, `MO-TRANSLATION`, `VA-MU-ADAPTER`, `VA-TRUE-FRAME-MEAN`, `VA-RESP-IDENTITIES`, `DEF-CUTOFF-TRACE-DEFECT` |  |
| `IN-CLIPPED-MATRIX-MEANS` | Conditional clipped matrix averages | `IN-CONTAINED-TRIANGLE-CUBES`, `IN-RESET-CHRONOLOGY`, `VA-TRUE-FRAME-MEAN` |  |
| `IN-COMPATIBLE-INTERPOLATION` | Loading-independent compatible interpolants | `IN-WHITNEY-ROOT-TILES`, `TR-DIAG-INTERPOLANT`, `VA-INTERPOLANT-LIFT`, `VA-ENERGYMAP`, `VA-COARSE-DUALITY` |  |
| `IN-CONTAINED-TRIANGLE-CUBES` | Contained-triangle cube comparison | `IN-WHITNEY-ROOT-TILES`, `VA-COARSE-DUALITY`, `VA-ENERGYMAP` |  |
| `IN-FIRST-LOCAL-BANK` | First local inverse cap | `IN-POINTWISE-ROOT`, `IN-FIXED-SELECTED-HEIGHT`, `IN-RESET-CHRONOLOGY`, `VA-TRUE-FRAME-MEAN`, `NU-IN-LOCAL-PROFILE`, `NU-IN-LOCAL-PROFILE-OUTPUTS`, `NU-IN-SELECTED-TAILS`, `NU-IN-HISTORY-ROOTS`, `NU-IN-LAYER-PROFILE`, `IN-POSITIVE-SPLIT-POPULATION-UNION` |  |
| `IN-FULL-RESPONSE-BANK` | Full-response reset at orders 64 and 128 | `IN-POINTWISE-ROOT`, `IN-FIXED-SELECTED-HEIGHT`, `IN-RESET-CHRONOLOGY`, `NU-IN-FULL-PROFILES`, `NU-IN-SELECTED-TAILS`, `NU-IN-LAYER-PROFILE`, `NU-IN-K0-LAYER-COMBINATION`, `NU-IN-LOCALIZATION-OFFSET` |  |
| `IN-FIXED-SELECTED-HEIGHT` | Fixed-entrance height selection | `IN-PLANAR-GEOMETRY`, `NU-IN-SELECTED-TAILS` |  |
| `IN-AO-CLIPPED-MATRIX` | conditional matrix and localization bounds | `IN-AO-RESTRICTION-RESET`, `IN-AO-PLANAR-GEOMETRY`, `IN-CLIPPED-MATRIX-MEANS`, `IN-WEIGHTED-LOCALIZATION`, `NU-IN-AO-BAND-POWERS` |  |
| `IN-AO-GAUSSIAN-TAILS` | physical Gaussian and selected tails | `IN-AO-PLANAR-GEOMETRY`, `IN-PHYSICAL-GAUSSIAN-ESTIMATES`, `NU-GA-WAVE-ALLORDER`, `NU-IN-SELECTED-TAILS`, `GA-WAVE-GATE`, `GA-SUP-MEAN` |  |
| `IN-AO-ORDER-RESET` | p-dependent all-real-order reset | `IN-ANCHOR-ADAPTER`, `IN-HISTORY-CONVERSION`, `IN-PLANAR-GEOMETRY`, `IN-AO-RESTRICTION-RESET`, `IN-AO-PLANAR-GEOMETRY`, `IN-AO-CLIPPED-MATRIX`, `IN-AO-GAUSSIAN-TAILS`, `IN-AO-POSITIVE-ASSEMBLY`, `DEF-NATIVE-STATE`, `SC-STRUCTURAL-CONTINUITY`, `MO-TRANSLATION`, `GA-WHOLE-ROOT`, `GA-MISSING-WAVE`, `GA-SUP-MEAN`, `VA-COARSE-DUALITY`, `VA-TRUE-FRAME-MEAN`, `VA-LEMMA-V`, `VA-INTERPOLANT-LIFT`, `TR-POINCARE-SENSITIVITY`, `NU-GA-WAVE-ALLORDER`, `NU-IN-DENSITY-GATE`, `NU-IN-AO-BAND-POWERS` | [`OrderReset.lean`](../ASDExplicitGamma/Inverse/OrderReset.lean) |
| `IN-AO-PLANAR-GEOMETRY` | stopped geometry and positive interpolation | `IN-AO-RESTRICTION-RESET`, `IN-COMPATIBLE-INTERPOLATION`, `NU-GA-WAVE-ALLORDER` |  |
| `IN-AO-POSITIVE-ASSEMBLY` | positive all-order root assembly | `IN-AO-CLIPPED-MATRIX`, `IN-AO-GAUSSIAN-TAILS`, `IN-AO-PLANAR-GEOMETRY`, `IN-AO-RESTRICTION-RESET`, `IN-POSITIVE-ROOT-ASSEMBLY`, `NU-IN-AO-BAND-POWERS` | [`AssemblyTraceProfileLp.lean`](../ASDExplicitGamma/Inverse/AssemblyTraceProfileLp.lean), [`AssemblyInverseProfile.lean`](../ASDExplicitGamma/Inverse/AssemblyInverseProfile.lean) |
| `IN-AO-RESTRICTION-RESET` | restriction and order bands | `IN-RESTRICTION-INDEPENDENCE`, `IN-STOPPED-PLANAR-CLUSTERS`, `IN-RESET-CHRONOLOGY`, `IN-HISTORY-CONVERSION` | [`AllOrderStoppedGeometry.lean`](../ASDExplicitGamma/Inverse/AllOrderStoppedGeometry.lean) |
| `IN-GLOBAL-BANK` | Part B global-bank interface | `IN-GLOBAL-INVERSE-BANK`, `IN-RESET-CHRONOLOGY`, `NU-IN-HISTORY-ROOTS`, `IN-POSITIVE-SPLIT-POPULATION-UNION` |  |
| `IN-GLOBAL-INVERSE-BANK` | Short-entrance global inverse bank | `IN-ONE-PASS-INVERSE-MEAN`, `IN-POINTWISE-ROOT`, `IN-FIXED-SELECTED-HEIGHT`, `IN-RESET-CHRONOLOGY`, `NU-IN-GLOBAL-PROFILE`, `NU-IN-HISTORY-ROOTS`, `NU-IN-LAYER-PROFILE`, `NU-IN-SELECTED-TAILS`, `NU-IN-512-TAIL`, `IN-POSITIVE-SPLIT-POPULATION-UNION` |  |
| `IN-HISTORY-CONVERSION` | buffer history supplies the L12 random history | `DEF-BUFFER40-HISTORY`, `DEF-NATIVE-STATE`, `MO-TRANSLATION`, `VA-COARSE-DUALITY`, `VA-SUBADDITIVITY`, `TR-HISTORY-MONOTONE`, `IN-RESET-CHRONOLOGY` |  |
| `IN-LOCAL-BANK` | Part B OLD local-bank interface | `IN-LOCAL-INVERSE-BANK`, `IN-RESET-CHRONOLOGY`, `NU-IN-LOCAL-PROFILE-OUTPUTS`, `IN-POSITIVE-SPLIT-POPULATION-UNION` |  |
| `IN-LOCAL-INVERSE-BANK` | OLD native local inverse bank | `IN-ONE-PASS-INVERSE-MEAN`, `IN-POINTWISE-ROOT`, `IN-FIXED-SELECTED-HEIGHT`, `IN-RESET-CHRONOLOGY`, `NU-IN-LOCAL-PROFILE`, `NU-IN-LOCAL-PROFILE-OUTPUTS`, `NU-IN-SELECTED-TAILS`, `NU-IN-HISTORY-ROOTS`, `NU-IN-LAYER-PROFILE`, `IN-POSITIVE-SPLIT-POPULATION-UNION` |  |
| `IN-MIXED-BRIDGE` | OLD/new correlated inverse/error bridge | `IN-GLOBAL-BANK`, `IN-LOCAL-BANK`, `IN-FULL-RESPONSE-BANK`, `IN-SOURCE-ROWS`, `NA-SOURCE-ROWS`, `IN-SOURCE-TRANSPORT`, `IN-SOURCE-ENERGY`, `IN-PARENT-GAP`, `IN-RAW-TRACE-TRANSPORT`, `NU-IN-TRACE-THETA`, `VA-COARSE-DUALITY`, `IN-RARE-SUM-EXPANSION`, `IN-WEAK-HISTORY-INEQUALITY` | [`BridgeLocalHistory.lean`](../ASDExplicitGamma/Inverse/BridgeLocalHistory.lean), [`BridgeObservables.lean`](../ASDExplicitGamma/Inverse/BridgeObservables.lean), [`BridgeGlobalBank.lean`](../ASDExplicitGamma/Inverse/BridgeGlobalBank.lean), [`MixedBridgeLocalBudget.lean`](../ASDExplicitGamma/Inverse/MixedBridgeLocalBudget.lean), [`MixedBridgeLocalTrace.lean`](../ASDExplicitGamma/Inverse/MixedBridgeLocalTrace.lean), [`MixedBridgeLocalSummability.lean`](../ASDExplicitGamma/Inverse/MixedBridgeLocalSummability.lean), [`MixedBridgeLocalCorrector.lean`](../ASDExplicitGamma/Inverse/MixedBridgeLocalCorrector.lean), [`MixedBridgeLocalTheta.lean`](../ASDExplicitGamma/Inverse/MixedBridgeLocalTheta.lean), [`MixedBridgeConclusion.lean`](../ASDExplicitGamma/Inverse/MixedBridgeConclusion.lean) |
| `IN-ONE-PASS-INVERSE-MEAN` | Causal one-pass inverse-block mean | `IN-FIRST-LOCAL-BANK`, `IN-RESET-CHRONOLOGY`, `DEF-NATIVE-STATE`, `GA-HEAT`, `VA-TRUE-FRAME-MEAN`, `VA-PROJECTED-SOURCE`, `VA-FORCED-SOURCE`, `IN-PURE-FLUX-GENERATOR`, `TR-POINCARE-SENSITIVITY`, `SC-STRUCTURAL-CONTINUITY`, `SC-WEAK-CORRIDORS`, `NU-SC-CLOCKS`, `NU-IN-ONE-PASS`, `NU-IN-ONE-PASS-COEFFICIENTS` |  |
| `IN-PARENT-GAP` | OLD parent-gap transport | `IN-GLOBAL-BANK`, `IN-LOCAL-BANK`, `IN-RAW-TRACE-TRANSPORT`, `IN-SOURCE-ENERGY`, `VA-COARSE-DUALITY`, `IN-RARE-SUM-EXPANSION` |  |
| `IN-PATHWISE-FRAME-MAP` | True-frame pathwise restoration | `SC-STRUCTURAL-CONTINUITY`, `VA-TRUE-FRAME-MEAN`, `IN-ANCHOR-ADAPTER`, `VA-COARSE-DUALITY` |  |
| `IN-PHYSICAL-GAUSSIAN-ESTIMATES` | Physical wave and selected-height Gaussian bounds | `GA-WAVE-GATE`, `GA-SUP-MEAN`, `IN-FIXED-SELECTED-HEIGHT`, `NU-GA-WAVE-FULL`, `NU-GA-WAVE-INVERSE`, `NU-GA-WAVE-ALLORDER`, `NU-IN-SELECTED-TAILS` |  |
| `IN-PLANAR-GEOMETRY` | Planar clusters and compatible Whitney cells | `MO-LOCAL-INDEPENDENCE`, `DEF-Q3-COV`, `MO-SPECTRAL`, `VA-MU-ADAPTER`, `TR-DIAG-INTERPOLANT`, `GA-SUP-MEAN`, `GA-WAVE-GATE`, `NU-IN-GAUSSIAN-GATES`, `IN-HISTORY-CONVERSION`, `IN-RESTRICTION-INDEPENDENCE`, `IN-STOPPED-PLANAR-CLUSTERS`, `IN-WHITNEY-ROOT-TILES`, `IN-COMPATIBLE-INTERPOLATION`, `IN-CONTAINED-TRIANGLE-CUBES`, `NU-IN-DENSITY-GATE` |  |
| `IN-POINTWISE-ROOT` | Positive pointwise root bound | `IN-ANCHOR-ADAPTER`, `IN-RESET-CHRONOLOGY`, `IN-HISTORY-CONVERSION`, `IN-PLANAR-GEOMETRY`, `IN-RESTRICTION-INDEPENDENCE`, `IN-STOPPED-PLANAR-CLUSTERS`, `IN-WHITNEY-ROOT-TILES`, `IN-COMPATIBLE-INTERPOLATION`, `IN-CONTAINED-TRIANGLE-CUBES`, `IN-CLIPPED-MATRIX-MEANS`, `IN-WEIGHTED-LOCALIZATION`, `IN-PHYSICAL-GAUSSIAN-ESTIMATES`, `IN-POSITIVE-ROOT-ASSEMBLY`, `DEF-NATIVE-STATE`, `SC-STRUCTURAL-CONTINUITY`, `VA-COARSE-DUALITY`, `VA-TRUE-FRAME-MEAN`, `VA-LEMMA-V`, `VA-INTERPOLANT-LIFT`, `VA-ENERGYMAP`, `TR-POINCARE-SENSITIVITY`, `GA-WHOLE-ROOT`, `GA-MISSING-WAVE`, `GA-SUP-MEAN`, `GA-HEAT`, `NU-IN-DENSITY-GATE`, `NU-IN-SELECTED-TAILS`, `NU-IN-LAYER-PROFILE`, `NU-IN-LOCALIZATION-OFFSET` |  |
| `IN-POSITIVE-ROOT-ASSEMBLY` | Positive error series and root moment assembly | `IN-COMPATIBLE-INTERPOLATION`, `IN-CLIPPED-MATRIX-MEANS`, `IN-WEIGHTED-LOCALIZATION`, `IN-PHYSICAL-GAUSSIAN-ESTIMATES`, `IN-PLANAR-GEOMETRY`, `NU-IN-SELECTED-TAILS`, `NU-IN-LAYER-PROFILE` |  |
| `IN-POSITIVE-SPLIT-POPULATION-UNION` | Positive split, L^256 truncation and finite-population union | `NU-IN-HISTORY-ROOTS` |  |
| `IN-PURE-FLUX-GENERATOR` | Positive pure-flux per-shell generator | `VA-FORCED-SOURCE`, `VA-PROJECTED-SOURCE`, `TR-POINCARE-SENSITIVITY`, `SC-WEAK-CORRIDORS`, `NU-SC-CLOCKS`, `NU-IN-ONE-PASS-COEFFICIENTS` |  |
| `IN-RARE-SUM-EXPANSION` | Expansion of rare factors before expectation | `IN-GLOBAL-BANK`, `IN-RAW-TRACE-TRANSPORT` | [`RareSum.lean`](../ASDExplicitGamma/Inverse/RareSum.lean) |
| `IN-RAW-TRACE-BAND` | h-dependent raw-trace band transport at h_*=134 | `DEF-NATIVE-STATE`, `IN-ANCHOR-ADAPTER`, `MO-SHELL-SCALING`, `SC-WEAK-CORRIDORS`, `NU-SC-CLOCKS`, `IN-LOCAL-INVERSE-BANK`, `IN-FULL-RESPONSE-BANK`, `IN-PATHWISE-FRAME-MAP`, `NU-IN-FULL-PROFILES`, `NU-NA-HISTORY-CONSTANTS`, `IN-RAW-TRACE-SHELL-TRANSPORT`, `NU-IN-ONE-PASS-COEFFICIENTS`, `NA-VANISHING-BRACKET`, `VA-COARSE-DUALITY`, `VA-SUBADDITIVITY`, `GA-TWO-PARAM`, `IN-PURE-FLUX-GENERATOR` | [`RawTraceTransport.lean`](../ASDExplicitGamma/Inverse/RawTraceTransport.lean) |
| `IN-RAW-TRACE-SHELL-TRANSPORT` | Per-shell finite-p constant-shear transport of the raw trace | `GA-HEAT`, `GA-MOMENT-CHAIN`, `GA-GENERATOR-SPLIT`, `VA-CONSTANT-SHEAR-TRACE`, `VA-PROJECTED-SOURCE`, `VA-FORCED-SOURCE`, `TR-POINCARE-SENSITIVITY`, `IN-LOCAL-INVERSE-BANK`, `IN-FULL-RESPONSE-BANK`, `NU-IN-ONE-PASS-COEFFICIENTS` | [`RawShellBandTransport.lean`](../ASDExplicitGamma/Inverse/RawShellBandTransport.lean) |
| `IN-RAW-TRACE-TRANSPORT` | Raw-trace implication proving the reserve | `IN-RAW-TRACE-BAND`, `IN-GLOBAL-BANK`, `NU-IN-TRACE-THETA` | [`RawTraceSpatialAverage.lean`](../ASDExplicitGamma/Inverse/RawTraceSpatialAverage.lean) |
| `IN-RESET-CHRONOLOGY` | Earlier-label inputs and root-relative reset ranges | `DEF-NATIVE-STATE`, `VA-TRUE-FRAME-MEAN` |  |
| `IN-RESET-INPUTS` | Part B reset-label adapter | `IN-RESET-CHRONOLOGY`, `DEF-NATIVE-STATE` |  |
| `IN-RESTRICTION-INDEPENDENCE` | Finite restriction-field independence | `MO-LOCAL-INDEPENDENCE`, `DEF-Q3-COV`, `MO-TRANSLATION` |  |
| `IN-SOURCE-ENERGY` | OLD source energy and slope interface | `IN-SOURCE-TRANSPORT`, `IN-SOURCE-ROWS`, `IN-LOCAL-BANK`, `TR-HISTORY-MONOTONE` | [`SourceEnergy.lean`](../ASDExplicitGamma/Inverse/SourceEnergy.lean) |
| `IN-SOURCE-ROWS` | OLD source-row interface for Part B | `NA-SOURCE-SMALLER-GAMMA`, `NU-NA-SOURCE-ROWS`, `IN-RESET-CHRONOLOGY`, `DEF-NATIVE-STATE` | [`SourceRows.lean`](../ASDExplicitGamma/Inverse/SourceRows.lean) |
| `IN-SOURCE-TRANSPORT` | One-shell OLD source transport | `IN-SOURCE-ROWS`, `IN-RESET-CHRONOLOGY`, `IN-LOCAL-BANK`, `IN-FULL-RESPONSE-BANK`, `MO-TRANSLATION`, `SC-STRUCTURAL-CONTINUITY` | [`SourceTransport.lean`](../ASDExplicitGamma/Inverse/SourceTransport.lean) |
| `IN-STOPPED-PLANAR-CLUSTERS` | Stopped marked-cluster radius and tail | `IN-RESTRICTION-INDEPENDENCE`, `GA-WAVE-GATE`, `NU-IN-DENSITY-GATE` |  |
| `IN-WEAK-HISTORY-INEQUALITY` | Intrinsic weak-history inequality V_l^2 <= D B* Hbar | `VA-COARSE-DUALITY`, `TR-INV-HISTORY`, `IN-RAW-TRACE-TRANSPORT` | [`WeakHistoryIneq.lean`](../ASDExplicitGamma/Inverse/WeakHistoryIneq.lean) |
| `IN-WEIGHTED-LOCALIZATION` | Weighted Bernstein and retained powers | `IN-WHITNEY-ROOT-TILES`, `IN-RESTRICTION-INDEPENDENCE`, `NU-IN-LAYER-PROFILE`, `NU-IN-LOCALIZATION-OFFSET`, `NU-IN-HISTORY-ROOTS`, `NU-IN-DENSITY-GATE`, `NU-IN-SELECTED-TAILS` |  |
| `IN-WHITNEY-ROOT-TILES` | Root-relative planar Whitney layers | `IN-STOPPED-PLANAR-CLUSTERS`, `NU-IN-LAYER-PROFILE` |  |

## Native moment systems and heat chains

| Step | Title | Uses | Lean |
|---|---|---|---|
| `NA-AFFINE-HEAT-GREEN-BOUND` | Affine moment-flow Green bound | `NA-VHEAT-BACKWARD-INEQUALITY`, `NA-AUGMENTED-DUHAMEL-COMPARISON` | [`HeatAffineGreen.lean`](../ASDExplicitGamma/Native/HeatAffineGreen.lean) |
| `NA-ANCHOR-ADAPTER` | Native observable and state identification | `DEF-ORDINARY-MEAN`, `DEF-ROOT20`, `DEF-STRONG20`, `DEF-BUFFER40-HISTORY`, `DEF-BUFFER-MEAN`, `DEF-NATIVE-STATE`, `IN-ANCHOR-ADAPTER`, `VA-MU-ADAPTER` |  |
| `NA-AUGMENTED-DUHAMEL-COMPARISON` | Duhamel comparison retaining the forcing |  |  |
| `NA-AUGMENTED-MOMENT-SYSTEMS` | Producer's 153 augmented systems | `NU-NA-HEAT-SYSTEMS` |  |
| `NA-COMPLETED-PREFIX-CAPS` | Positive finite-prefix mean and weak-row comparison | `NA-GENERIC-SOURCE-ROWS`, `NA-PARENT-BOUNDARY-CHARGE`, `NU-NA-SOURCE-ROWS` | [`PrefixCapsFinal.lean`](../ASDExplicitGamma/Native/PrefixCapsFinal.lean) |
| `NA-COOPERATIVE-HEAT-SYSTEM` | Augmented comparison for 153 positive moment systems | `NA-AUGMENTED-MOMENT-SYSTEMS`, `NA-AUGMENTED-DUHAMEL-COMPARISON`, `NA-VANISHING-BRACKET`, `VA-LEMMA-V`, `GA-HEAT`, `VA-DEFECT`, `VA-TRUE-FRAME-MEAN`, `NA-INITIAL-HEAT-MOMENTS` |  |
| `NA-FINITE-PROFILE` | OLD/NEW bank roles for finite profiles | `IN-GLOBAL-BANK`, `IN-LOCAL-BANK`, `IN-RESET-CHRONOLOGY`, `NU-IN-GLOBAL-PROFILE`, `NU-IN-LOCAL-PROFILE-OUTPUTS`, `NU-IN-HISTORY-ROOTS`, `SC-RESOLVENT-IDENTITY`, `IN-POSITIVE-SPLIT-POPULATION-UNION` |  |
| `NA-FINITE-RANK-LIMIT` | Finite-rank heat limit at fixed diffusivity | `NA-AUGMENTED-DUHAMEL-COMPARISON`, `NA-INITIAL-HEAT-MOMENTS`, `NA-HEAT-REMAINDER-CONTROL`, `IN-PATHWISE-FRAME-MAP` | [`HeatFiniteRankLimit.lean`](../ASDExplicitGamma/Native/HeatFiniteRankLimit.lean), [`HeatTrueFrameCurve.lean`](../ASDExplicitGamma/Native/HeatTrueFrameCurve.lean), [`HeatCooperativeFiniteRankLimit.lean`](../ASDExplicitGamma/Native/HeatCooperativeFiniteRankLimit.lean), [`HeatTrueFrameCooperativeCurve.lean`](../ASDExplicitGamma/Native/HeatTrueFrameCooperativeCurve.lean) |
| `NA-FULL-RESPONSE-ROWS` | Part B full64 response interface | `IN-FULL-RESPONSE-BANK`, `IN-RESET-CHRONOLOGY`, `NU-IN-FULL-PROFILES`, `NU-IN-HISTORY-ROOTS` |  |
| `NA-GENERIC-SOURCE-ROWS` | Earlier-label generic and refined source rows | `NA-ANCHOR-ADAPTER`, `IN-RESET-CHRONOLOGY`, `IN-LOCAL-INVERSE-BANK`, `VA-TRUE-FRAME-MEAN`, `DEF-NATIVE-STATE` | [`GenericSourceUnconditionalRows.lean`](../ASDExplicitGamma/Native/GenericSourceUnconditionalRows.lean) |
| `NA-HEAT-REMAINDER-CONTROL` | Nonconstant remainder and raw forcing control | `NA-VANISHING-BRACKET`, `IN-LOCAL-INVERSE-BANK`, `IN-FULL-RESPONSE-BANK`, `NU-IN-FULL-PROFILES` |  |
| `NA-INITIAL-HEAT-MOMENTS` | Initial vector-heat moment bounds | `NA-ANCHOR-ADAPTER`, `NU-NA-HISTORY-CONSTANTS`, `NA-ONE-PASS-CHAIN` | [`HeatInitialRefinedRangeFinalGen.lean`](../ASDExplicitGamma/Native/HeatInitialRefinedRangeFinalGen.lean) |
| `NA-MOLECULAR-BOX` | Fixed-label molecular native estimate | `SC-MOLECULAR-LOWER`, `SC-MOLECULAR-UPPER`, `SC-MOLECULAR-FIVE-FOUR`, `DEF-ORDINARY-MEAN`, `DEF-ROOT20`, `DEF-STRONG20`, `DEF-BUFFER40-HISTORY`, `DEF-BUFFER-MEAN`, `DEF-NATIVE-STATE`, `MO-SHELL-SCALING`, `MO-SPECTRAL`, `MO-PRODUCT-Q3-D4-GAUGE`, `VA-MU-ADAPTER`, `GA-OLDER-FIELD`, `VA-TRUE-FRAME-MEAN`, `IN-HISTORY-CONVERSION`, `NU-NA-MOLECULAR-STARTUP` |  |
| `NA-MOLECULAR-STARTUP` | Left-half-line molecular base | `NA-MOLECULAR-BOX`, `NU-NA-MOLECULAR-STARTUP`, `SC-MOLECULAR-LOWER`, `SC-MOLECULAR-UPPER` |  |
| `NA-ONE-PASS-CHAIN` | Causal 1.59 to 0.1494 to 1.4732 chain | `IN-FIRST-LOCAL-BANK`, `IN-ONE-PASS-INVERSE-MEAN`, `IN-LOCAL-INVERSE-BANK`, `IN-GLOBAL-INVERSE-BANK`, `NU-IN-ONE-PASS` |  |
| `NA-PARENT-BOUNDARY-CHARGE` | Boundary-fixed old parent rows | `NA-GENERIC-SOURCE-ROWS`, `IN-LOCAL-INVERSE-BANK`, `VA-COARSE-DUALITY`, `VA-TRUE-FRAME-MEAN`, `VA-FORCED-SOURCE`, `NU-NA-Q1-AND-PREFIX` | [`ParentRowFinalComposition.lean`](../ASDExplicitGamma/Native/ParentRowFinalComposition.lean) |
| `NA-PARENT-PREFIX` | Boundary-fixed parent rows through depth sixteen | `NA-SOURCE-SMALLER-GAMMA`, `NA-PARENT-BOUNDARY-CHARGE`, `NA-COMPLETED-PREFIX-CAPS`, `NU-NA-Q1-AND-PREFIX`, `NU-NA-SOURCE-ROWS`, `SC-UPPER-T0-QUADRATURE`, `NU-SC-UPPER-T0-REPLAY`, `IN-RESET-CHRONOLOGY`, `VA-TRUE-FRAME-MEAN` |  |
| `NA-Q1-BOUNDARY-CHARGE` | Boundary-fixed old q1 estimate | `NA-GENERIC-SOURCE-ROWS`, `IN-LOCAL-INVERSE-BANK`, `VA-COARSE-DUALITY`, `VA-TRUE-FRAME-MEAN`, `VA-FORCED-SOURCE`, `NU-NA-Q1-AND-PREFIX` | [`OldSignedCompletedQ1.lean`](../ASDExplicitGamma/Native/OldSignedCompletedQ1.lean) |
| `NA-REFINED-HEAT` | Native refined-child backward-heat step | `NA-COOPERATIVE-HEAT-SYSTEM`, `NA-VANISHING-BRACKET`, `NA-AUGMENTED-MOMENT-SYSTEMS`, `NA-INITIAL-HEAT-MOMENTS`, `NA-AFFINE-HEAT-GREEN-BOUND`, `NA-HEAT-REMAINDER-CONTROL`, `NA-FINITE-RANK-LIMIT`, `NA-VHEAT-BACKWARD-INEQUALITY`, `DEF-NATIVE-STATE`, `NA-Q1-BOUNDARY-CHARGE`, `SC-WEAK-CORRIDORS`, `GA-GENERATOR-SPLIT`, `GA-REMAINDER-HEAT`, `IN-LOCAL-INVERSE-BANK`, `IN-FULL-RESPONSE-BANK`, `IN-PATHWISE-FRAME-MAP`, `VA-LEMMA-V`, `NU-NA-HEAT-SYSTEMS`, `NU-IN-REFINED-CHILD-COEFFICIENTS`, `NU-NA-Q1-AND-PREFIX` | [`HeatStepNodeClosed.lean`](../ASDExplicitGamma/Native/HeatStepNodeClosed.lean), [`BandWeighted.lean`](../ASDExplicitGamma/Gaussian/BandWeighted.lean) |
| `NA-RETURNS` | Native returns and distinct carried caps | `NA-REFINED-HEAT`, `NA-ONE-PASS-CHAIN`, `IN-ONE-PASS-INVERSE-MEAN`, `IN-PATHWISE-FRAME-MAP`, `NU-NA-RETURNS`, `NU-NA-HEAT-SYSTEMS`, `NU-NA-Q1-AND-PREFIX`, `NU-NA-HISTORY-CONSTANTS`, `NU-NA-TAIL-DOMAIN` | [`ReturnsFinal.lean`](../ASDExplicitGamma/Native/ReturnsFinal.lean) |
| `NA-SOURCE-ROWS` | Completed-source means and weak inverse rows | `NA-ANCHOR-ADAPTER`, `NA-GENERIC-SOURCE-ROWS`, `NA-SOURCE-SMALLER-GAMMA`, `IN-LOCAL-INVERSE-BANK`, `IN-RESET-CHRONOLOGY`, `VA-TRUE-FRAME-MEAN`, `VA-COARSE-DUALITY`, `NU-NA-SOURCE-ROWS` | [`SourceChainRows.lean`](../ASDExplicitGamma/Native/SourceChainRows.lean) |
| `NA-SOURCE-SMALLER-GAMMA` | continuation for source rows, q1, and parent rows | `IN-LOCAL-INVERSE-BANK`, `IN-GLOBAL-INVERSE-BANK`, `IN-ONE-PASS-INVERSE-MEAN`, `IN-RESET-CHRONOLOGY`, `IN-RESET-INPUTS`, `IN-FULL-RESPONSE-BANK`, `NU-IN-FULL-PROFILES`, `NU-IN-GLOBAL-PROFILE`, `NU-IN-LOCAL-PROFILE-OUTPUTS`, `NU-IN-HISTORY-ROOTS`, `IN-RAW-TRACE-TRANSPORT`, `NA-FULL-RESPONSE-ROWS`, `NA-GENERIC-SOURCE-ROWS`, `NA-Q1-BOUNDARY-CHARGE`, `NA-PARENT-BOUNDARY-CHARGE`, `NA-COMPLETED-PREFIX-CAPS`, `NU-NA-Q1-AND-PREFIX`, `NU-NA-SOURCE-ROWS`, `NU-SC-UPPER-T0-REPLAY`, `VA-TRUE-FRAME-MEAN`, `DEF-NATIVE-STATE`, `SC-STRUCTURAL-CONTINUITY` | [`SourceChainSmallerGamma.lean`](../ASDExplicitGamma/Native/SourceChainSmallerGamma.lean) |
| `NA-STEP` | Target-N native component update | `DEF-NATIVE-STATE`, `NA-ANCHOR-ADAPTER`, `NA-SOURCE-ROWS`, `NA-PARENT-PREFIX`, `NA-RETURNS`, `NA-THETA-SCALING`, `IN-RESET-CHRONOLOGY`, `IN-FIRST-LOCAL-BANK`, `IN-ONE-PASS-INVERSE-MEAN`, `IN-GLOBAL-INVERSE-BANK`, `IN-LOCAL-INVERSE-BANK`, `IN-FULL-RESPONSE-BANK`, `IN-PATHWISE-FRAME-MAP`, `NU-NA-HISTORY-CONSTANTS`, `NU-NA-TAIL-DOMAIN` | [`StepNode.lean`](../ASDExplicitGamma/Native/StepNode.lean) |
| `NA-THETA-SCALING` | Proportional native outputs | `NA-RETURNS`, `NA-SOURCE-SMALLER-GAMMA`, `IN-ONE-PASS-INVERSE-MEAN`, `IN-PATHWISE-FRAME-MAP`, `NU-NA-THETA-EXPONENTS` | [`ReturnsFinalTheta.lean`](../ASDExplicitGamma/Native/ReturnsFinalTheta.lean) |
| `NA-VANISHING-BRACKET` | Lemma V remainder-noise bracket application | `NA-ANCHOR-ADAPTER`, `VA-LEMMA-V`, `VA-LEMMA-V-H1`, `VA-LEMMA-V-H2-BAND`, `VA-LEMMA-V-H2-REMAINDER`, `VA-LEMMA-V-H2-SINGLE`, `GA-HEAT`, `VA-DEFECT`, `VA-TRUE-FRAME-MEAN` |  |
| `NA-VHEAT-BACKWARD-INEQUALITY` | Full-polynomial backward heat differential inequality | `GA-BACKWARD-HEAT`, `NA-VANISHING-BRACKET`, `NA-INITIAL-HEAT-MOMENTS`, `IN-LOCAL-INVERSE-BANK`, `IN-FULL-RESPONSE-BANK` | [`HeatVHEATSourceNodeFinalGen.lean`](../ASDExplicitGamma/Native/HeatVHEATSourceNodeFinalGen.lean), [`HeatVHEATSourceNode.lean`](../ASDExplicitGamma/Native/HeatVHEATSourceNode.lean) |

## Main return

| Step | Title | Uses | Lean |
|---|---|---|---|
| `MA-AFFINE` | Stationary affine term | `MO-LOCAL-INDEPENDENCE`, `MO-BFLAT-CAPS`, `VA-TRUE-FRAME-MEAN`, `VA-SUBADDITIVITY`, `IN-GLOBAL-INVERSE-BANK`, `MA-FLAT-FIELD`, `NU-MA-LOCAL-CAPS`, `NU-MO-BFLAT-CAPS` | [`AffineStationary.lean`](../ASDExplicitGamma/Main/AffineStationary.lean), [`AffineObserverExpectation.lean`](../ASDExplicitGamma/Main/AffineObserverExpectation.lean), [`AffineObserverFrame.lean`](../ASDExplicitGamma/Main/AffineObserverFrame.lean), [`AffineMatrixMoments.lean`](../ASDExplicitGamma/Main/AffineMatrixMoments.lean), [`AffineBlockTraceMeans.lean`](../ASDExplicitGamma/Main/AffineBlockTraceMeans.lean), [`AffineActualTrace.lean`](../ASDExplicitGamma/Main/AffineActualTrace.lean), [`AffineLowerRightMean.lean`](../ASDExplicitGamma/Main/AffineLowerRightMean.lean), [`AffineFlatLoss.lean`](../ASDExplicitGamma/Main/AffineFlatLoss.lean), [`AffineFlatBoundary.lean`](../ASDExplicitGamma/Main/AffineFlatBoundary.lean), [`AffineInverseTrace.lean`](../ASDExplicitGamma/Main/AffineInverseTrace.lean), [`AffineScalarReduction.lean`](../ASDExplicitGamma/Main/AffineScalarReduction.lean) |
| `MA-CHRONOLOGY` | Forty insertion composition from certified leaves | `MA-PANEL-COMPARISON`, `MA-PANEL-ENCLOSURE`, `MA-FRAME-RESTORATION`, `MA-SHELL-CLOCK`, `MA-ENVELOPE-A`, `MA-ENVELOPE-XI`, `IN-SOURCE-ROWS`, `NA-SOURCE-ROWS`, `MO-BFLAT-CAPS`, `NU-MO-BFLAT-CAPS`, `CO-TRIANGULAR-129`, `NU-MA-PANEL-8`, `NU-MA-RECURRENCE-FIELDS`, `NU-SC-COLD40-COMPAT`, `EXT-ASDExplicitGamma-Numerics-MainReturn-mainReturn-certificate`, `EXT-ASDExplicitGamma-Numerics-div-le-ceilDiv`, `EXT-ASDExplicitGamma-Numerics-ceilDiv-mono-left`, `STEP-MA-CHRONOLOGY-V-MONOTONE` |  |
| `MA-DIRECTIONAL-COVARIANCE` | Directional shell covariance envelope | `MA-ENVELOPE-XI`, `IN-LOCAL-INVERSE-BANK`, `MO-PRODUCT-Q3-D4-GAUGE`, `TR-PAIRED-BESSEL`, `TR-BROKEN-NORMS` | [`DirectionalCovarianceTrace.lean`](../ASDExplicitGamma/Main/DirectionalCovarianceTrace.lean), [`DirectionalPhysicalFlux.lean`](../ASDExplicitGamma/Main/DirectionalPhysicalFlux.lean), [`DirectionalGram.lean`](../ASDExplicitGamma/Main/DirectionalGram.lean), [`DirectionalSymmetry.lean`](../ASDExplicitGamma/Main/DirectionalSymmetry.lean), [`DirectionalExpected.lean`](../ASDExplicitGamma/Main/DirectionalExpected.lean) |
| `MA-DIRECTIONAL-PHYSICAL-FLUX` | Physical-flux directional bound | `MO-PRODUCT-Q3-D4-GAUGE`, `MA-MULTIPLIER-MOMENTS`, `TR-KP-RIESZ`, `VA-COARSE-DUALITY`, `MA-DIRECTIONAL-COVARIANCE` | [`EnvelopeHSharpOfHist.lean`](../ASDExplicitGamma/Main/EnvelopeHSharpOfHist.lean), [`DirectionalPhysicalFlux.lean`](../ASDExplicitGamma/Main/DirectionalPhysicalFlux.lean), [`DirectionalGram.lean`](../ASDExplicitGamma/Main/DirectionalGram.lean), [`DirectionalSymmetry.lean`](../ASDExplicitGamma/Main/DirectionalSymmetry.lean), [`DirectionalExpected.lean`](../ASDExplicitGamma/Main/DirectionalExpected.lean) |
| `MA-DIRICHLET-HESSIAN-SQUARE` | Dirichlet Hessian identity on the square |  |  |
| `MA-E-CONCAVITY` | Decreasing concave error profile | `MA-E-LINEAR`, `MA-E-SOURCE-SQUARE`, `MA-E-COVARIANCE`, `MA-E-OSCILLATION`, `MA-E-PARENT-GAP`, `MA-E-FOURLOAD-AGGREGATE`, `MA-E-REMAINDER-FEEDBACK`, `MA-ENVELOPE-A`, `MA-ENVELOPE-XI`, `MA-ENVELOPE-H` | [`ErrorSupportCorrected.lean`](../ASDExplicitGamma/Main/ErrorSupportCorrected.lean) |
| `MA-E-COVARIANCE` | Half-coefficient covariance cross term | `MA-INTERPOLANT-CONTRACTION`, `MA-MULTIPLIER-PRODUCT`, `MA-DIRECTIONAL-COVARIANCE`, `MA-FLAT-FIELD`, `TR-PAIRED-BESSEL`, `TR-KP-RIESZ`, `IN-MIXED-BRIDGE`, `VA-COMPATIBLE-COERCIVITY`, `VA-PROJECTED-SOURCE`, `VA-FORCED-SOURCE` | [`EnvelopeHSharpOfHist.lean`](../ASDExplicitGamma/Main/EnvelopeHSharpOfHist.lean), [`HotCovNodeFinal.lean`](../ASDExplicitGamma/Main/HotCovNodeFinal.lean) |
| `MA-E-FOURLOAD-AGGREGATE` | Four-load inverse aggregate | `MA-MULTIPLIER-PRODUCT`, `MA-MULTIPLIER-MOMENTS`, `MA-MIXED-BRIDGE`, `IN-GLOBAL-INVERSE-BANK`, `IN-MIXED-BRIDGE`, `MA-E-PARENT-GAP`, `MA-FLAT-FIELD`, `MA-DIRECTIONAL-COVARIANCE` | [`EnvelopeHSharpOfHist.lean`](../ASDExplicitGamma/Main/EnvelopeHSharpOfHist.lean), [`EBottomCovarianceActualLaw.lean`](../ASDExplicitGamma/Main/EBottomCovarianceActualLaw.lean), [`ELinearActualLaw.lean`](../ASDExplicitGamma/Main/ELinearActualLaw.lean) |
| `MA-E-LINEAR` | Linear mean/oscillation energy term | `IN-GLOBAL-INVERSE-BANK`, `IN-LOCAL-INVERSE-BANK`, `IN-FULL-RESPONSE-BANK`, `MA-DIRECTIONAL-COVARIANCE`, `MA-DIRECTIONAL-PHYSICAL-FLUX`, `MA-FLAT-FIELD`, `MA-MULTIPLIER-MOMENTS`, `MA-MULTIPLIER-PRODUCT`, `NU-MA-LOCAL-CAPS` | [`EnvelopeHSharpOfHist.lean`](../ASDExplicitGamma/Main/EnvelopeHSharpOfHist.lean), [`ELinearActualLaw.lean`](../ASDExplicitGamma/Main/ELinearActualLaw.lean) |
| `MA-E-OSCILLATION` | Source oscillation term | `MA-MULTIPLIER-PRODUCT`, `MA-FLAT-FIELD`, `MA-MULTIPLIER-MOMENTS`, `IN-GLOBAL-INVERSE-BANK`, `IN-FULL-RESPONSE-BANK` | [`EnvelopeHSharpOfHist.lean`](../ASDExplicitGamma/Main/EnvelopeHSharpOfHist.lean), [`HotEOscillationNode.lean`](../ASDExplicitGamma/Main/HotEOscillationNode.lean) |
| `MA-E-PARENT-GAP` | Four-load parent-gap remainder | `MA-ENVELOPE-XI`, `MA-MIXED-BRIDGE`, `MO-BFLAT-CAPS`, `VA-TRUE-FRAME-MEAN`, `IN-MIXED-BRIDGE`, `NU-MO-BFLAT-CAPS`, `NU-MA-LOCAL-CAPS` | [`EParentGapActualLaw.lean`](../ASDExplicitGamma/Main/EParentGapActualLaw.lean), [`HotTopCovarianceBill.lean`](../ASDExplicitGamma/Native/HotTopCovarianceBill.lean), [`HotCovarianceBetaCap.lean`](../ASDExplicitGamma/Main/HotCovarianceBetaCap.lean) |
| `MA-E-REMAINDER-FEEDBACK` | Positive remainder feedback | `MA-E-SOURCE-SQUARE`, `MA-MULTIPLIER-PRODUCT`, `MA-MIXED-BRIDGE`, `IN-GLOBAL-INVERSE-BANK`, `IN-MIXED-BRIDGE` | [`EnvelopeHSharpOfHist.lean`](../ASDExplicitGamma/Main/EnvelopeHSharpOfHist.lean), [`HotRemainderFeedbackNode.lean`](../ASDExplicitGamma/Main/HotRemainderFeedbackNode.lean), [`HotRemainderFeedbackMoments.lean`](../ASDExplicitGamma/Main/HotRemainderFeedbackMoments.lean) |
| `MA-E-SOURCE-SQUARE` | Positive source-square term | `IN-GLOBAL-INVERSE-BANK`, `IN-MIXED-BRIDGE`, `MA-MIXED-BRIDGE`, `MA-ENVELOPE-H`, `NU-MA-LOCAL-CAPS` | [`EnvelopeHSharpOfHist.lean`](../ASDExplicitGamma/Main/EnvelopeHSharpOfHist.lean), [`HotESourceSquareNode.lean`](../ASDExplicitGamma/Main/HotESourceSquareNode.lean) |
| `MA-ENVELOPE-A` | OLD-law mean envelope | `MA-PARTIAL-INSERTION`, `GA-HEAT`, `NA-SOURCE-ROWS`, `IN-RESET-INPUTS`, `IN-FULL-RESPONSE-BANK`, `MO-AMPLITUDE-INVARIANCE`, `IN-LOCAL-INVERSE-BANK`, `DEF-MA-LOADS-AND-SLOPES` | [`EnvelopeA.lean`](../ASDExplicitGamma/Main/EnvelopeA.lean), [`EnvelopeASlope.lean`](../ASDExplicitGamma/Main/EnvelopeASlope.lean) |
| `MA-ENVELOPE-H` | OLD-law history envelope | `MA-HEAT-IDENTITY`, `GA-HEAT`, `DEF-NATIVE-STATE`, `IN-LOCAL-INVERSE-BANK`, `IN-RESET-INPUTS`, `IN-FULL-RESPONSE-BANK` | [`EnvelopeHTransport.lean`](../ASDExplicitGamma/Main/EnvelopeHTransport.lean), [`EnvelopeHProfile.lean`](../ASDExplicitGamma/Main/EnvelopeHProfile.lean), [`EnvelopeHProfileArithmetic.lean`](../ASDExplicitGamma/Main/EnvelopeHProfileArithmetic.lean), [`EnvelopeHFixedFrameGenerator.lean`](../ASDExplicitGamma/Main/EnvelopeHFixedFrameGenerator.lean), [`RawShellFixedFrameGeneralP20.lean`](../ASDExplicitGamma/Inverse/RawShellFixedFrameGeneralP20.lean), [`EnvelopeHControlComparison.lean`](../ASDExplicitGamma/Main/EnvelopeHControlComparison.lean), [`EnvelopeHMaxHistory.lean`](../ASDExplicitGamma/Main/EnvelopeHMaxHistory.lean) |
| `MA-ENVELOPE-XI` | Weighted inverse envelope | `IN-MIXED-BRIDGE`, `IN-GLOBAL-INVERSE-BANK`, `IN-LOCAL-INVERSE-BANK`, `IN-RAW-TRACE-TRANSPORT`, `IN-FULL-RESPONSE-BANK`, `NA-SOURCE-ROWS`, `MA-ENVELOPE-A` | [`EnvelopeXIActual.lean`](../ASDExplicitGamma/Main/EnvelopeXIActual.lean) |
| `MA-FLAT-FIELD` | Flat-field H¹ and oscillation bounds | `VA-TRUE-FRAME-MEAN`, `VA-SUBADDITIVITY`, `MO-BFLAT-CAPS`, `NU-MO-BFLAT-CAPS`, `NU-MA-LOCAL-CAPS`, `STEP-MA-FLAT-FIELD-H1-BOUNDS`, `MO-Q3-DERIVATIVE-MOMENTS`, `MO-HELMHOLTZ-MULTIPLIER`, `TR-POINCARE-CELL-CONSTANTS`, `TR-SENSITIVITY-TAIL`, `TR-BROKEN-NORMS`, `MA-SHELL-CLOCK`, `MA-DIRICHLET-HESSIAN-SQUARE` | [`FlatFieldSourceCaps.lean`](../ASDExplicitGamma/Main/FlatFieldSourceCaps.lean), [`FlatFieldH1Bounds.lean`](../ASDExplicitGamma/Main/FlatFieldH1Bounds.lean), [`FlatFieldCellGeometry.lean`](../ASDExplicitGamma/Main/FlatFieldCellGeometry.lean) |
| `MA-FRAME-RESTORATION` | Completed-law frame return | `VA-TRUE-FRAME-MEAN`, `VA-SUBADDITIVITY`, `SC-STRUCTURAL-CONTINUITY`, `NU-SC-FRAME-RATIOS` |  |
| `MA-GENERATOR-HYPOTHESES` | Annealed assembly and main differential inequality | `MA-HEAT-IDENTITY`, `MA-PATHWISE-HESSIAN`, `MA-TRACE-LOWER-GENERATOR`, `MA-SHELL-CLOCK`, `MA-E-LINEAR`, `MA-E-SOURCE-SQUARE`, `MA-E-COVARIANCE`, `MA-E-OSCILLATION`, `MA-E-PARENT-GAP`, `MA-E-FOURLOAD-AGGREGATE`, `MA-E-REMAINDER-FEEDBACK`, `MA-AFFINE`, `MA-INVERSE-DEFICIT`, `MA-ENVELOPE-A`, `MA-ENVELOPE-XI`, `MA-ENVELOPE-H`, `MA-DIRECTIONAL-COVARIANCE`, `MA-FLAT-FIELD`, `MA-MULTIPLIER-MOMENTS`, `MA-MIXED-BRIDGE`, `MA-INTERPOLANT-CONTRACTION`, `MA-MULTIPLIER-PRODUCT`, `VA-TRUE-FRAME-MEAN`, `VA-SUBADDITIVITY`, `IN-FULL-RESPONSE-BANK`, `IN-RAW-TRACE-TRANSPORT`, `NU-MA-LOCAL-CAPS`, `DEF-MA-LOADS-AND-SLOPES` | [`ObsNodes.lean`](../ASDExplicitGamma/Main/ObsNodes.lean) |
| `MA-HEAT-IDENTITY` | True-law generator and absolute continuity | `MA-PARTIAL-INSERTION`, `GA-HEAT`, `GA-RESPONSE-ANALYTIC`, `GA-FIXED-NU`, `DEF-TRACE-DEFECT`, `DEF-CUTOFF-TRACE-DEFECT` |  |
| `MA-INTERPOLANT-CONTRACTION` | Weak interpolant contraction | `TR-DIAG-INTERPOLANT`, `TR-INTERPOLANT-ESTIMATES` |  |
| `MA-INVERSE-DEFICIT` | Absolute inverse-deficit branch | `MA-HEAT-IDENTITY`, `MA-TRACE-LOWER-GENERATOR`, `IN-GLOBAL-INVERSE-BANK`, `IN-FULL-RESPONSE-BANK`, `VA-TRUE-FRAME-MEAN` | [`ObsMainRangeNodes.lean`](../ASDExplicitGamma/Main/ObsMainRangeNodes.lean), [`InverseDeficitInitial.lean`](../ASDExplicitGamma/Main/InverseDeficitInitial.lean), [`InverseDeficitHeatAdapter.lean`](../ASDExplicitGamma/Main/InverseDeficitHeatAdapter.lean), [`InverseDeficitODE.lean`](../ASDExplicitGamma/Main/InverseDeficitODE.lean), [`InverseDeficitBank.lean`](../ASDExplicitGamma/Main/InverseDeficitBank.lean), [`InverseLowerCenteredGlobalBank.lean`](../ASDExplicitGamma/Main/InverseLowerCenteredGlobalBank.lean), [`InverseDeficitHistoryBound.lean`](../ASDExplicitGamma/Main/InverseDeficitHistoryBound.lean) |
| `MA-MIXED-BRIDGE` | OLD/new correlated bridge | `IN-MIXED-BRIDGE`, `IN-GLOBAL-INVERSE-BANK`, `IN-LOCAL-INVERSE-BANK`, `IN-RESET-INPUTS`, `IN-RAW-TRACE-TRANSPORT`, `VA-TRUE-FRAME-MEAN` | [`EnvelopeHSharpOfHist.lean`](../ASDExplicitGamma/Main/EnvelopeHSharpOfHist.lean) |
| `MA-MULTIPLIER-MOMENTS` | History multiplier moments | `MA-ENVELOPE-H`, `MA-FLAT-FIELD`, `MA-MULTIPLIER-PRODUCT` | [`EnvelopeHSharpOfHist.lean`](../ASDExplicitGamma/Main/EnvelopeHSharpOfHist.lean), [`MultiplierMoments.lean`](../ASDExplicitGamma/Main/MultiplierMoments.lean), [`MultiplierMatrixBound.lean`](../ASDExplicitGamma/Main/MultiplierMatrixBound.lean) |
| `MA-MULTIPLIER-PRODUCT` | Row and column multiplier products | `TR-PRODUCT`, `TR-INTERPOLANT-ESTIMATES`, `TR-POINCARE-CELL-CONSTANTS`, `MO-Q3-DERIVATIVE-MOMENTS`, `VA-INTERPOLANT-ESTIMATES`, `NU-MA-LOCAL-CAPS` |  |
| `MA-ORDINARY-RETURN` | Ordinary mean at the target label | `MA-GENERATOR-HYPOTHESES`, `MA-CHRONOLOGY`, `MA-THETA-CONTINUATION`, `CO-TRIANGULAR-129`, `NA-ANCHOR-ADAPTER`, `IN-RESET-INPUTS`, `NA-SOURCE-ROWS`, `DEF-NATIVE-STATE`, `STEP-MA-ORDINARY-RETURN-LINTEGRAL` | [`MainLaneClosed.lean`](../ASDExplicitGamma/Main/MainLaneClosed.lean), [`OrdinaryReturnIntegral.lean`](../ASDExplicitGamma/Main/OrdinaryReturnIntegral.lean), [`OrdinaryReturnEndpoint.lean`](../ASDExplicitGamma/Main/OrdinaryReturnEndpoint.lean) |
| `MA-PANEL-COMPARISON` | Affine panel comparison |  |  |
| `MA-PANEL-ENCLOSURE` | Whole-panel generator enclosure | `MA-GENERATOR-HYPOTHESES`, `MA-E-CONCAVITY`, `NU-MA-PANEL-8`, `NU-MA-RECURRENCE-FIELDS` | [`PanelEnclosureClosed.lean`](../ASDExplicitGamma/Main/PanelEnclosureClosed.lean) |
| `MA-PARTIAL-INSERTION` | Fixed old frame and actual heat law | `DEF-PLANAR-Q3-GAUSSIAN`, `MO-CUTOFF-IDENTIFICATION`, `GA-CM-REALIZATION`, `IN-ANCHOR-ADAPTER` |  |
| `MA-PATHWISE-HESSIAN` | Pathwise second-variation and Hessian bounds | `MA-PARTIAL-INSERTION`, `MA-SHELL-CLOCK`, `VA-NILPOTENT-SHEAR`, `VA-LOCALIZED-SHEAR`, `VA-INTERPOLANT-LIFT` | [`LocalizedHessian.lean`](../ASDExplicitGamma/Main/LocalizedHessian.lean), [`LocalizedHessianQ3Residual.lean`](../ASDExplicitGamma/Main/LocalizedHessianQ3Residual.lean), [`Q3ResidualHilbertSchmidt.lean`](../ASDExplicitGamma/Main/Q3ResidualHilbertSchmidt.lean), [`PathwiseHessianLocalizedCovariance.lean`](../ASDExplicitGamma/Main/PathwiseHessianLocalizedCovariance.lean), [`PathwiseHessianKernelBounds.lean`](../ASDExplicitGamma/Main/PathwiseHessianKernelBounds.lean), [`PathwiseHessianLocalizedMeasurability.lean`](../ASDExplicitGamma/Main/PathwiseHessianLocalizedMeasurability.lean), [`PathwiseHessianParentCovariance.lean`](../ASDExplicitGamma/Main/PathwiseHessianParentCovariance.lean), [`PathwiseHessianResponseCovariance.lean`](../ASDExplicitGamma/Main/PathwiseHessianResponseCovariance.lean), [`PathwiseHessianSignedCovariance.lean`](../ASDExplicitGamma/Main/PathwiseHessianSignedCovariance.lean) |
| `MA-SHELL-CLOCK` | Old-label variance clock | `DEF-NATIVE-STATE`, `MO-SHELL-SCALING`, `NU-SC-CLOCKS` |  |
| `MA-THETA-CONTINUATION` | Smaller positive gamma | `MA-E-CONCAVITY`, `MA-ENVELOPE-A`, `MA-ENVELOPE-XI`, `MA-ENVELOPE-H`, `MA-CHRONOLOGY`, `MA-INVERSE-DEFICIT`, `CO-THETA-SCALING`, `SC-EXACT-LAW-SCALING` | [`ThetaGeneratorReturn.lean`](../ASDExplicitGamma/Main/ThetaGeneratorReturn.lean) |
| `MA-TRACE-LOWER-GENERATOR` | Pathwise inverse-trace lower bound | `MA-PATHWISE-HESSIAN`, `NU-MA-LOCAL-CAPS` | [`ObsLowerFinal.lean`](../ASDExplicitGamma/Main/ObsLowerFinal.lean), [`InverseLowerAlgebra.lean`](../ASDExplicitGamma/Main/InverseLowerAlgebra.lean), [`InverseHessianActualQ3.lean`](../ASDExplicitGamma/Main/InverseHessianActualQ3.lean), [`InverseHessianCenteredQ3.lean`](../ASDExplicitGamma/Main/InverseHessianCenteredQ3.lean), [`InverseHessianSourceComponents.lean`](../ASDExplicitGamma/Main/InverseHessianSourceComponents.lean), [`InverseObservableGauge.lean`](../ASDExplicitGamma/Main/InverseObservableGauge.lean), [`InverseLowerProjection.lean`](../ASDExplicitGamma/Main/InverseLowerProjection.lean), [`InverseLowerRowPairing.lean`](../ASDExplicitGamma/Main/InverseLowerRowPairing.lean), [`InverseLowerCenteredRowPairing.lean`](../ASDExplicitGamma/Main/InverseLowerCenteredRowPairing.lean), [`InverseLowerVariation.lean`](../ASDExplicitGamma/Main/InverseLowerVariation.lean), [`InverseLowerRowBound.lean`](../ASDExplicitGamma/Main/InverseLowerRowBound.lean), [`InverseLowerCenteredRowBound.lean`](../ASDExplicitGamma/Main/InverseLowerCenteredRowBound.lean), [`InverseLowerCenteredProjectedQ3.lean`](../ASDExplicitGamma/Main/InverseLowerCenteredProjectedQ3.lean), [`InverseLowerCenteredEnergy.lean`](../ASDExplicitGamma/Main/InverseLowerCenteredEnergy.lean), [`InverseLowerCenteredProjectionTrace.lean`](../ASDExplicitGamma/Main/InverseLowerCenteredProjectionTrace.lean), [`InverseLowerCenteredFeedbackTrace.lean`](../ASDExplicitGamma/Main/InverseLowerCenteredFeedbackTrace.lean), [`InverseLowerCenteredSourceTrace.lean`](../ASDExplicitGamma/Main/InverseLowerCenteredSourceTrace.lean), [`InverseLowerCenteredPairTrace.lean`](../ASDExplicitGamma/Main/InverseLowerCenteredPairTrace.lean), [`PathwiseHessianResponseCovariance.lean`](../ASDExplicitGamma/Main/PathwiseHessianResponseCovariance.lean), [`InverseLowerCenteredBankRow.lean`](../ASDExplicitGamma/Main/InverseLowerCenteredBankRow.lean) |

## All-order consequence

| Step | Title | Uses | Lean |
|---|---|---|---|
| `AO-ALL-PROFILE` | Inverse root and all-(p) trace profile | `IN-AO-ORDER-RESET`, `GA-WHOLE-ROOT`, `AO-CHI-SQUARE`, `GA-MISSING-WAVE`, `GA-SUP-MEAN`, `VA-TRUE-FRAME-MEAN`, `SC-STRUCTURAL-CONTINUITY`, `NU-AO-PROFILE-GATES`, `DEF-NATIVE-STATE` |  |
| `AO-CHI-SQUARE` | Planar Gaussian square moment | `GA-CM-REALIZATION`, `GA-CM-SERIES`, `MO-Q3-IDENTITIES` |  |
| `AO-CIR-AVERAGING` | Finite-even averaging constant 144 | `AO-CHI-SQUARE`, `MO-LOCAL-INDEPENDENCE`, `MO-FOUR-COLOR`, `NU-AO-CIR-GATES` |  |
| `AO-CIR-BRACKET-4` | Adapter to Part A bracket | `GA-GENERATOR-BOUNDS`, `AO-CIR-GENERATOR-19`, `NU-AO-CIR-GATES` |  |
| `AO-CIR-FINITE-EVEN` | Finite-even induction and real-order fill | `AO-CIR-AVERAGING`, `AO-CIR-MOMENT-TRANSPORT`, `SC-STRUCTURAL-CONTINUITY`, `IN-PATHWISE-FRAME-MAP`, `DEF-NATIVE-STATE`, `AO-ALL-PROFILE`, `NU-AO-PROFILE-GATES`, `NU-AO-CIR-GATES`, `NU-AO-TRANSFER-GATES`, `STEP-AO-CIR-SMALL-GAMMA-SEED` |  |
| `AO-CIR-GENERATOR-19` | Adapter to Part A generator | `GA-GENERATOR-BOUNDS`, `NU-AO-CIR-GATES` |  |
| `AO-CIR-MOMENT-TRANSPORT` | Adapter to Part A all-real-order transport | `GA-P12`, `AO-CIR-GENERATOR-19`, `AO-CIR-BRACKET-4` |  |
| `AO-HISTORY-SUM` | All-order normalized depth history | `AO-OBSERVABLE-ADAPTER`, `AO-PER-DEPTH`, `NU-AO-BULK-HISTORY`, `NU-AO-RARE-RATES`, `DEF-NATIVE-STATE` |  |
| `AO-MARKOV-COUPLED` | Coupled two-term tail at real orders | `AO-HISTORY-SUM`, `NU-AO-BULK-HISTORY`, `NU-AO-RARE-RATES`, `EXT-Algsuperdiff-Section3-Observable-measurable-cutoffHomogenizationError`, `EXT-Algsuperdiff-Section3-Observable-cutoffHomogenizationError-nonneg` |  |
| `AO-OBSERVABLE-ADAPTER` | observable to trace-defect depth sum | `VA-MU-ADAPTER`, `VA-COARSE-DUALITY`, `MO-TRANSLATION`, `DEF-TRACE-DEFECT`, `EXT-Algsuperdiff-Section3-Observable-cutoffHomogenizationError`, `EXT-Algsuperdiff-Section3-Observable-cutoffHomogenizationError-ae-eq-homogenizationE`, `EXT-Homogenization-Book-Ch02-doubledResponseJ-eq-half-responseJ-adjoint-sum`, `EXT-Homogenization-Book-Ch02-responseMagicIdentitiesTheory`, `EXT-Algsuperdiff-Section3-Observable-measurable-cutoffHomogenizationError`, `EXT-Algsuperdiff-Section3-Observable-cutoffHomogenizationError-nonneg` |  |
| `AO-PER-DEPTH` | Bound at each real order and depth | `AO-ALL-PROFILE`, `AO-CIR-FINITE-EVEN`, `AO-CIR-MOMENT-TRANSPORT`, `DEF-NATIVE-STATE`, `IN-AO-ORDER-RESET`, `MO-TRANSLATION`, `SC-STRUCTURAL-CONTINUITY`, `IN-PATHWISE-FRAME-MAP`, `NU-AO-FRAME-GATES`, `NU-AO-PROFILE-GATES`, `NU-AO-RARE-RATES`, `NU-AO-TRANSFER-GATES` |  |

## Joint induction step

| Step | Title | Uses | Lean |
|---|---|---|---|
| `JO-BUFFER40-HISTORY-N` | Buffer-history component at (N) | `NA-RETURNS`, `NA-STEP`, `NU-NA-RETURNS`, `NU-JO-RETURN-CAPS`, `DEF-NATIVE-STATE` |  |
| `JO-BUFFER40-MEAN-N` | Separate buffer-mean component at (N) | `NA-RETURNS`, `NA-STEP`, `NU-NA-RETURNS`, `NU-JO-RETURN-CAPS`, `DEF-NATIVE-STATE` |  |
| `JO-LOWER-SCALAR-N` | Lower scalar components at (N) | `SC-LOWER-CORRIDOR`, `SC-ONE-SHELL-RECIPROCAL-DROP`, `SC-RECIPROCAL-TELESCOPE`, `SC-COLD-RECIPROCAL-NORMALIZATION`, `SC-RECIPROCAL-MOLECULAR-CAP`, `CO-TRIANGULAR-129`, `SC-STRUCTURAL-CONTINUITY`, `CO-THETA-SCALING`, `DEF-NATIVE-STATE` | [`LowerScalarNClosed.lean`](../ASDExplicitGamma/Joint/LowerScalarNClosed.lean) |
| `JO-MOLECULAR-BASE` | Left-half-line base for induction | `NA-MOLECULAR-STARTUP`, `NA-MOLECULAR-BOX`, `NU-NA-MOLECULAR-STARTUP`, `SC-ENTRANCE-MOLECULAR-STARTUP`, `SC-MOLECULAR-FIVE-FOUR`, `MO-SHELL-SCALING`, `NU-JO-RETURN-CAPS`, `DEF-NATIVE-STATE` |  |
| `JO-ORDINARY-MEAN` | Target mean component | `MA-ORDINARY-RETURN`, `CO-TRIANGULAR-129`, `DEF-NATIVE-STATE`, `IN-RESET-INPUTS`, `NA-SOURCE-ROWS` | [`MainLaneClosed.lean`](../ASDExplicitGamma/Main/MainLaneClosed.lean), [`OrdinaryMeanN.lean`](../ASDExplicitGamma/Joint/OrdinaryMeanN.lean) |
| `JO-ROOT20-N` | Singleton-root component at (N) | `NA-RETURNS`, `NA-STEP`, `NU-NA-RETURNS`, `DEF-NATIVE-STATE` |  |
| `JO-STEP-ASSEMBLY` | Eight components at one target | `JO-LOWER-SCALAR-N`, `JO-ORDINARY-MEAN`, `JO-STRONG20-N`, `JO-ROOT20-N`, `JO-BUFFER40-HISTORY-N`, `JO-BUFFER40-MEAN-N`, `JO-UPPER-SCALAR-N`, `DEF-NATIVE-STATE` | [`StepAssembly.lean`](../ASDExplicitGamma/Joint/StepAssembly.lean) |
| `JO-STRONG20-N` | Strong-history component at (N) | `NA-RETURNS`, `NA-THETA-SCALING`, `NA-STEP`, `NU-JO-RETURN-CAPS`, `DEF-NATIVE-STATE` |  |
| `JO-UPPER-SCALAR-N` | Upper scalar component at (N) | `SC-UPPER-STEP`, `SC-LONGBLOCK-TRIAL`, `SC-UPPER-SIGNAL-INTERVAL`, `SC-MOLECULAR-FIVE-FOUR`, `NU-SC-UPPER-ERROR`, `NU-SC-UPPER-BARRIER`, `DEF-NATIVE-STATE` | [`UpperScalarN.lean`](../ASDExplicitGamma/Joint/UpperScalarN.lean) |

## Intermediate steps

| Step | Title | Uses | Lean |
|---|---|---|---|
| `STEP-AO-CIR-SMALL-GAMMA-SEED` |  | `DEF-NATIVE-STATE`, `DEF-SHELL-VARIANCE`, `AO-CHI-SQUARE`, `VA-MU-ADAPTER` |  |
| `STEP-MA-CHRONOLOGY-V-MONOTONE` |  | `MA-SHELL-CLOCK`, `MA-E-CONCAVITY`, `MA-ENVELOPE-A`, `MA-ENVELOPE-XI`, `MA-ENVELOPE-H`, `MA-INVERSE-DEFICIT`, `MA-AFFINE`, `DEF-MA-LOADS-AND-SLOPES`, `MA-FLAT-FIELD`, `MA-E-PARENT-GAP`, `MA-MULTIPLIER-PRODUCT` | [`ObsChronoFinal.lean`](../ASDExplicitGamma/Main/ObsChronoFinal.lean) |
| `STEP-MA-FLAT-FIELD-H1-BOUNDS` |  | `MO-BFLAT-CAPS`, `NU-MA-LOCAL-CAPS` | [`FlatFieldH1Bounds.lean`](../ASDExplicitGamma/Main/FlatFieldH1Bounds.lean) |
| `STEP-MA-ORDINARY-RETURN-LINTEGRAL` |  | `NA-ANCHOR-ADAPTER`, `DEF-ORDINARY-MEAN`, `DEF-CUTOFF-TRACE-DEFECT`, `DEF-TRACE-DEFECT`, `MA-THETA-CONTINUATION`, `GA-FIXED-NU`, `GA-OLDER-FIELD` | [`MainLaneClosed.lean`](../ASDExplicitGamma/Main/MainLaneClosed.lean) |

## Alternative routes

| Step | Title | Uses | Lean |
|---|---|---|---|
| `RT-GA-WAVE-GATE-FULL` | Wave gate via the full-response row | `NU-GA-WAVE-FULL` |  |
| `RT-GA-WAVE-GATE-INVERSE` | Wave gate via the inverse-response row | `NU-GA-WAVE-INVERSE` |  |
| `RT-GA-WAVE-GATE-ALLORDER` | Wave gate via the all-order row | `NU-GA-WAVE-ALLORDER` |  |
| `RT-LV-H2-BAND` | Lemma V with the stationary-band row | `VA-LEMMA-V-H2-BAND` |  |
| `RT-LV-H2-REMAINDER` | Lemma V with the remainder row | `VA-LEMMA-V-H2-REMAINDER` |  |
| `RT-LV-H2-SINGLE` | Lemma V with the single-direction row | `VA-LEMMA-V-H2-SINGLE` |  |

## Numerical certificates

| Step | Title | Uses | Lean |
|---|---|---|---|
| `NU-AO-BULK-HISTORY` | Exact history coefficients (2^{29}) and 8608 |  |  |
| `NU-AO-CIR-GATES` | Exact transport and finite-even gates |  |  |
| `NU-AO-FRAME-GATES` | Adapter to the scalar-frame gates | `NU-SC-FRAME-FACTOR`, `NU-SC-FRAME-RATIOS`, `NU-SC-FRAME-COSTS`, `SC-STRUCTURAL-CONTINUITY` |  |
| `NU-AO-PROFILE-GATES` | Exact all-order profile coefficients | `MO-BFLAT-CAPS`, `NU-MO-BFLAT-CAPS`, `NU-IN-AO-BAND-POWERS`, `NU-IN-LAYER-PROFILE` |  |
| `NU-AO-RARE-RATES` | Internal 1350, displayed 1500, and source 8192 | `NU-AO-BULK-HISTORY`, `NU-AO-TRANSFER-GATES` |  |
| `NU-AO-TRANSFER-GATES` | Real-order branches and allocations | `NU-AO-PROFILE-GATES`, `NU-AO-CIR-GATES` |  |
| `NU-BRIDGE-RATIO` | Exact rational gate for the scalar corridor | `DEF-GAMMA-ZERO`, `DEF-SHELL-VARIANCE`, `MO-J4-CSTAR` |  |
| `NU-CO-COLD-LAGS` | Exact outward cold recurrence certificate | `CO-TRIANGULAR-129`, `NU-CO-ROOT2`, `NU-CO-SQRT3-BOUND`, `NU-CO-PLATEAU-TAIL` | [`Certificate.lean`](../ASDExplicitGamma/Numerics/Cold/Certificate.lean), [`RealDominance.lean`](../ASDExplicitGamma/Numerics/Cold/RealDominance.lean) |
| `NU-CO-PLATEAU-PI` | Square and cutoff constants |  |  |
| `NU-CO-PLATEAU-TAIL` | Plateau weight tails | `NU-CO-SQRT3-BOUND` |  |
| `NU-CO-ROOT2` | Cold L2 interpolation root |  | [`Basic.lean`](../ASDExplicitGamma/Numerics/Cold/Basic.lean) |
| `NU-CO-SQRT3-BOUND` | Cold tail radical replacement |  | [`Basic.lean`](../ASDExplicitGamma/Numerics/Cold/Basic.lean) |
| `NU-GA-MU-STAR` | Exact matrix-eigenvalue bound mu_* < 19 |  |  |
| `NU-GA-WAVE-FULL` | Exact full-response wave-gate margins | `DEF-WAVE-GATE-CONSTANTS`, `DEF-GAMMA-ZERO` |  |
| `NU-GA-WAVE-INVERSE` | Exact inverse-response wave-gate margins | `DEF-WAVE-GATE-CONSTANTS`, `DEF-GAMMA-ZERO` |  |
| `NU-GA-WAVE-ALLORDER` | Exact all-order wave-gate margin | `DEF-WAVE-GATE-CONSTANTS`, `DEF-GAMMA-ZERO` |  |
| `NU-IN-512-TAIL` | Positive 512-factorial tail and remainder targets |  | [`Tails.lean`](../ASDExplicitGamma/Numerics/Inverse/Tails.lean), [`TailSoundness.lean`](../ASDExplicitGamma/Numerics/Inverse/TailSoundness.lean) |
| `NU-IN-DENSITY-GATE` | Exact rare-density input at the protected entrances |  | [`MomentsInverse.lean`](../ASDExplicitGamma/Numerics/Inverse/MomentsInverse.lean), [`MomentsFull.lean`](../ASDExplicitGamma/Numerics/Inverse/MomentsFull.lean), [`RealBounds.lean`](../ASDExplicitGamma/Numerics/Inverse/RealBounds.lean) |
| `NU-IN-FULL-MOMENT-RECURRENCE` | Full-response truncated moment recurrence | `NU-IN-DENSITY-GATE` | [`MomentsFull.lean`](../ASDExplicitGamma/Numerics/Inverse/MomentsFull.lean) |
| `NU-IN-FULL-PROFILES` | Full64/full128 trace-profile checks | `NU-IN-FULL-MOMENT-RECURRENCE`, `NU-IN-LAYER-PROFILE`, `NU-IN-LOCALIZATION-OFFSET`, `NU-IN-HISTORY-ROOTS`, `NU-IN-K0-LAYER-COMBINATION`, `NU-IN-512-TAIL` | [`Full64.lean`](../ASDExplicitGamma/Numerics/Inverse/Full64.lean), [`Full128.lean`](../ASDExplicitGamma/Numerics/Inverse/Full128.lean), [`FullHistory.lean`](../ASDExplicitGamma/Numerics/Inverse/FullHistory.lean) |
| `NU-IN-AO-BAND-POWERS` | Corrected all-order band contractions |  | [`Scalars.lean`](../ASDExplicitGamma/Numerics/Inverse/Scalars.lean) |
| `NU-IN-GAUSSIAN-GATES` | Part-A Gaussian gate margin adapter | `NU-GA-WAVE-FULL`, `NU-GA-WAVE-INVERSE`, `NU-GA-WAVE-ALLORDER`, `GA-WAVE-GATE`, `DEF-WAVE-GATE-CONSTANTS` | [`RealBounds.lean`](../ASDExplicitGamma/Numerics/Inverse/RealBounds.lean) |
| `NU-IN-GLOBAL-PROFILE` | Global inverse output comparisons | `NU-IN-DENSITY-GATE`, `NU-IN-HISTORY-ROOTS`, `NU-IN-LAYER-PROFILE`, `NU-IN-512-TAIL`, `NU-IN-LOCAL-PROFILE` | [`ProfileGlobal.lean`](../ASDExplicitGamma/Numerics/Inverse/ProfileGlobal.lean) |
| `NU-IN-HISTORY-ROOTS` | Exact geometric and finite-population factors | `NU-IN-SELECTED-TAILS` | [`Basic.lean`](../ASDExplicitGamma/Numerics/Inverse/Basic.lean), [`RealBounds.lean`](../ASDExplicitGamma/Numerics/Inverse/RealBounds.lean) |
| `NU-IN-K0-LAYER-COMBINATION` | Corrected consumed K0 layer comparison | `NU-IN-LAYER-PROFILE` | [`Full64.lean`](../ASDExplicitGamma/Numerics/Inverse/Full64.lean), [`Full128.lean`](../ASDExplicitGamma/Numerics/Inverse/Full128.lean) |
| `NU-IN-LAYER-PROFILE` | Exact planar weights and generating functions |  | [`Basic.lean`](../ASDExplicitGamma/Numerics/Inverse/Basic.lean), [`Layers.lean`](../ASDExplicitGamma/Numerics/Inverse/Layers.lean) |
| `NU-IN-LOCAL-PROFILE` | Inverse-only finite-profile arithmetic | `NU-IN-DENSITY-GATE`, `NU-IN-SELECTED-TAILS`, `NU-IN-LAYER-PROFILE`, `NU-IN-HISTORY-ROOTS` | [`MomentsInverse.lean`](../ASDExplicitGamma/Numerics/Inverse/MomentsInverse.lean), [`ProfileLocal.lean`](../ASDExplicitGamma/Numerics/Inverse/ProfileLocal.lean) |
| `NU-IN-LOCAL-PROFILE-OUTPUTS` | Local inverse and first-pass comparisons | `NU-IN-LOCAL-PROFILE`, `NU-IN-HISTORY-ROOTS`, `NU-IN-512-TAIL` | [`ProfileLocal.lean`](../ASDExplicitGamma/Numerics/Inverse/ProfileLocal.lean), [`ProfileFirst.lean`](../ASDExplicitGamma/Numerics/Inverse/ProfileFirst.lean) |
| `NU-IN-LOCALIZATION-OFFSET` | Exact p=64/128 localization payment | `NU-IN-LAYER-PROFILE` | [`Localization64.lean`](../ASDExplicitGamma/Numerics/Inverse/Localization64.lean), [`Localization128.lean`](../ASDExplicitGamma/Numerics/Inverse/Localization128.lean) |
| `NU-IN-ONE-PASS` | One-pass excess rational comparison | `NU-IN-LOCAL-PROFILE-OUTPUTS` | [`Scalars.lean`](../ASDExplicitGamma/Numerics/Inverse/Scalars.lean) |
| `NU-IN-ONE-PASS-COEFFICIENTS` | Uniform-clock covariance coefficient sums |  | [`Covariance0.lean`](../ASDExplicitGamma/Numerics/Inverse/Covariance0.lean) |
| `NU-IN-REFINED-CHILD-COEFFICIENTS` | q=1 refined transport row |  | [`Covariance1.lean`](../ASDExplicitGamma/Numerics/Inverse/Covariance1.lean) |
| `NU-IN-SELECTED-TAILS` | Exact finite-height and infinite selected tails | `NU-IN-GAUSSIAN-GATES`, `NU-IN-512-TAIL` | [`SelectedTails.lean`](../ASDExplicitGamma/Numerics/Inverse/SelectedTails.lean), [`Tails.lean`](../ASDExplicitGamma/Numerics/Inverse/Tails.lean) |
| `NU-IN-TRACE-THETA` | Theta-scaled trace-series coefficient | `NU-IN-FULL-PROFILES`, `NU-IN-HISTORY-ROOTS` | [`Scalars.lean`](../ASDExplicitGamma/Numerics/Inverse/Scalars.lean), [`RealBounds.lean`](../ASDExplicitGamma/Numerics/Inverse/RealBounds.lean) |
| `NU-JO-RETURN-CAPS` | Native return and induction arithmetic | `NU-MA-PANEL-8`, `NU-NA-RETURNS`, `NU-NA-MOLECULAR-STARTUP`, `NU-SC-UPPER-STARTUP` |  |
| `NU-MA-LOCAL-CAPS` | Main covariance and decimal majorants | `DEF-GAMMA-ZERO`, `DEF-THETA` |  |
| `NU-MA-PANEL-8` | 320 leaf formula bounds and composition certificate | `NU-MA-LOCAL-CAPS`, `NU-MA-RECURRENCE-FIELDS`, `EXT-ASDExplicitGamma-Numerics-MainReturn-mainReturn-certificate` |  |
| `NU-MA-RECURRENCE-FIELDS` | Kernel checks for the recurrence fields of the 320 leaves |  |  |
| `NU-MO-BFLAT-CAPS` | WP12 exact finite-mode q3 cap obligation | `MO-Q3-IDENTITIES` |  |
| `NU-NA-HEAT-SYSTEMS` | 153 exact positive Taylor enclosures | `NU-NA-HEAT-SYSTEMS-10-60`, `NU-NA-HEAT-SYSTEMS-61-111`, `NU-NA-HEAT-SYSTEMS-112-161`, `NU-NA-HEAT-SYSTEMS-GAP-1` |  |
| `NU-NA-HEAT-SYSTEMS-10-60` | First 51 augmented heat systems |  |  |
| `NU-NA-HEAT-SYSTEMS-112-161` | Last 50 augmented heat systems |  |  |
| `NU-NA-HEAT-SYSTEMS-61-111` | Middle 51 augmented heat systems |  |  |
| `NU-NA-HEAT-SYSTEMS-GAP-1` | Gap-one refined-child system |  |  |
| `NU-NA-HISTORY-CONSTANTS` | Native history and average constants |  |  |
| `NU-NA-MOLECULAR-STARTUP` | Exact small-variance startup thresholds | `MO-SHELL-SCALING`, `MO-SPECTRAL`, `MO-PRODUCT-Q3-D4-GAUGE`, `VA-MU-ADAPTER`, `GA-OLDER-FIELD`, `VA-TRUE-FRAME-MEAN`, `SC-MOLECULAR-LOWER`, `SC-MOLECULAR-FIVE-FOUR` |  |
| `NU-NA-Q1-AND-PREFIX` | Endpoint 512-panel boundary-fixed q1 and parent enclosures |  |  |
| `NU-NA-RETURNS` | Endpoint native return and carried-cap comparisons | `NU-NA-HEAT-SYSTEMS`, `NU-NA-Q1-AND-PREFIX`, `NU-NA-HISTORY-CONSTANTS`, `NU-NA-TAIL-DOMAIN` |  |
| `NU-NA-SOURCE-ROWS` | Six endpoint source means and weak inverse caps | `NU-NA-Q1-AND-PREFIX` |  |
| `NU-NA-TAIL-DOMAIN` | Native infinite-history domain and tails | `NU-NA-HISTORY-CONSTANTS` |  |
| `NU-NA-THETA-EXPONENTS` | Exact proportional-order exponents |  |  |
| `NU-SC-BFLAT-MONOTONE-TAIL` | flat-tail coefficient | `MO-BFLAT-CAPS` | [`Frames.lean`](../ASDExplicitGamma/Numerics/Scalar/Frames.lean) |
| `NU-SC-BRIDGE-RESERVE` | Mixed bridge reserve | `NU-SC-LOG3-SMALL` | [`Basic.lean`](../ASDExplicitGamma/Numerics/Scalar/Basic.lean) |
| `NU-SC-CLOCKS` | Clock margins of the lower corridor | `NU-SC-LOG3-SMALL` | [`Basic.lean`](../ASDExplicitGamma/Numerics/Scalar/Basic.lean) |
| `NU-SC-COLD40-COMPAT` | Cold-40 endpoint compatibility with the main return | `NU-CO-COLD-LAGS` |  |
| `NU-SC-LOWER-COERCIVITY` | Variational constants of the lower corridor |  | [`Readable.lean`](../ASDExplicitGamma/Numerics/Scalar/Readable.lean) |
| `NU-SC-LOWER-COMBINE` | Quartic assembly constants | `NU-SC-LOWER-COERCIVITY`, `NU-SC-LOWER-FACTORS`, `NU-SC-H-SOURCE`, `SC-NEW-RESOLVENT-DEFECT`, `SC-NEW-RESOLVENT-COMBINE` | [`Lower.lean`](../ASDExplicitGamma/Numerics/Scalar/Lower.lean) |
| `NU-SC-LOWER-FACTORS` | Pure and mixed factors |  | [`Readable.lean`](../ASDExplicitGamma/Numerics/Scalar/Readable.lean) |
| `NU-SC-UPPER-GEOMETRY` | Long-block geometric gate |  | [`Readable.lean`](../ASDExplicitGamma/Numerics/Scalar/Readable.lean) |
| `NU-SC-UPPER-ROW` | Long-block source-row constants |  | [`Readable.lean`](../ASDExplicitGamma/Numerics/Scalar/Readable.lean) |
| `NU-SC-FRAME-COSTS` | Frame restoration endpoints | `NU-SC-LOG3-SMALL` | [`Frames.lean`](../ASDExplicitGamma/Numerics/Scalar/Frames.lean) |
| `NU-SC-FRAME-FACTOR` | Exponential one-shell factor | `NU-SC-LOG3-SMALL` | [`Frames.lean`](../ASDExplicitGamma/Numerics/Scalar/Frames.lean) |
| `NU-SC-FRAME-RATIOS` | Structural ratio constants |  | [`Basic.lean`](../ASDExplicitGamma/Numerics/Scalar/Basic.lean), [`Endpoints.lean`](../ASDExplicitGamma/Numerics/Scalar/Endpoints.lean) |
| `NU-SC-H-SOURCE` | Source strong-history cap |  | [`Basic.lean`](../ASDExplicitGamma/Numerics/Scalar/Basic.lean), [`Endpoints.lean`](../ASDExplicitGamma/Numerics/Scalar/Endpoints.lean) |
| `NU-SC-K-MARGIN` | Exact lower-gain margin | `SC-OLD-HESSIAN-TRIAL`, `SC-NEW-RESOLVENT-COMBINE`, `NU-SC-LOWER-COMBINE`, `SC-LOWER-INPUT-BRIDGE` | [`Lower.lean`](../ASDExplicitGamma/Numerics/Scalar/Lower.lean) |
| `NU-SC-LOG-TAIL` | Atanh series tail |  |  |
| `NU-SC-LOG3-SMALL` | Logarithm comparisons for scalar clocks | `NU-SC-LOG-TAIL` | [`Basic.lean`](../ASDExplicitGamma/Numerics/Scalar/Basic.lean) |
| `NU-SC-LOG3-UPPER` | Minimal one-shell logarithm bound | `NU-SC-LOG3-SMALL` | [`Basic.lean`](../ASDExplicitGamma/Numerics/Scalar/Basic.lean) |
| `NU-SC-OLD-GROUPED-REMAINDER` | Grouped scalar error and local-bank remainder |  | [`Basic.lean`](../ASDExplicitGamma/Numerics/Scalar/Basic.lean), [`Endpoints.lean`](../ASDExplicitGamma/Numerics/Scalar/Endpoints.lean) |
| `NU-SC-UPPER-BARRIER` | Concave squared barrier | `NU-SC-UPPER-SIGNAL-ARITH` | [`Basic.lean`](../ASDExplicitGamma/Numerics/Scalar/Basic.lean), [`Frames.lean`](../ASDExplicitGamma/Numerics/Scalar/Frames.lean) |
| `NU-SC-UPPER-ERROR` | Complete long-block error enclosure | `NU-SC-UPPER-T0-REPLAY`, `NU-SC-LOG3-SMALL` | [`Frames.lean`](../ASDExplicitGamma/Numerics/Scalar/Frames.lean), [`Upper.lean`](../ASDExplicitGamma/Numerics/Scalar/Upper.lean) |
| `NU-SC-UPPER-SIGNAL-ARITH` | Signal endpoint comparisons | `NU-SC-LOG3-SMALL` |  |
| `NU-SC-UPPER-STARTUP` | Molecular startup inequality |  | [`Basic.lean`](../ASDExplicitGamma/Numerics/Scalar/Basic.lean), [`MolecularAlgebra.lean`](../ASDExplicitGamma/Scalar/MolecularAlgebra.lean) |
| `NU-SC-UPPER-T0-REPLAY` | Exact depth-14 parent-prefix replay |  |  |

## External inputs

| Step | Title | Uses | Lean |
|---|---|---|---|
| `EXT-Algsuperdiff-Frozen-Assumptions-ShellField` | Algsuperdiff..Assumptions.ShellField |  |  |
| `EXT-Algsuperdiff-Frozen-Assumptions-ShellField-zeroShellLaw` | Algsuperdiff..Assumptions.ShellField.zeroShellLaw |  |  |
| `EXT-Algsuperdiff-Frozen-Assumptions-ShellField-zeroShellPotentialCorrector` | Algsuperdiff..Assumptions.ShellField.zeroShellPotentialCorrector |  |  |
| `EXT-Algsuperdiff-Frozen-Assumptions-ShellLawPrefix-independent` | Algsuperdiff..Assumptions.ShellLawPrefix.independent |  |  |
| `EXT-Algsuperdiff-Frozen-Assumptions-ShellLawPrefix-marginal-scaling` | Algsuperdiff..Assumptions.ShellLawPrefix.marginal_scaling |  |  |
| `EXT-Algsuperdiff-Frozen-Section24-existsUnique-coarseMatrixDerivative` | Algsuperdiff..Section24.existsUnique_coarseMatrixDerivative |  |  |
| `EXT-Algsuperdiff-Frozen-Section3-inductionState` | Algsuperdiff..Section3.inductionState |  |  |
| `EXT-Algsuperdiff-Probability-Stationary-stationaryPotentialProjection` | Algsuperdiff.Probability.Stationary.stationaryPotentialProjection |  |  |
| `EXT-Algsuperdiff-Section3-Annealed-sigmaBar` | Algsuperdiff.Section3.Annealed.sigmaBar |  |  |
| `EXT-Algsuperdiff-Section3-Annealed-sigmaBar-characterization` | Algsuperdiff.Section3.Annealed.sigmaBar_characterization |  |  |
| `EXT-Algsuperdiff-Section3-Cutoff-CutoffSample` | Algsuperdiff.Section3.Cutoff.CutoffSample |  |  |
| `EXT-Algsuperdiff-Section3-Cutoff-coefficientCutoff` | Algsuperdiff.Section3.Cutoff.coefficientCutoff |  |  |
| `EXT-Algsuperdiff-Section3-Cutoff-coefficientCutoffLaw-stationary-real` | Algsuperdiff.Section3.Cutoff.coefficientCutoffLaw_stationary_real |  |  |
| `EXT-Algsuperdiff-Section3-Cutoff-cutoffSampleLaw` | Algsuperdiff.Section3.Cutoff.cutoffSampleLaw |  |  |
| `EXT-Algsuperdiff-Section3-Disorder-cstar-characterization` | Algsuperdiff.Section3.Disorder.cstar_characterization |  |  |
| `EXT-Algsuperdiff-Section3-Observable-cutoffHomogenizationError` | Algsuperdiff.Section3.Observable.cutoffHomogenizationError |  |  |
| `EXT-Algsuperdiff-Section3-Observable-cutoffHomogenizationError-ae-eq-homogenizationE` | Algsuperdiff.Section3.Observable.cutoffHomogenizationError_ae_eq_homogenizationErrorOnCube |  |  |
| `EXT-Algsuperdiff-Section3-Observable-cutoffHomogenizationError-nonneg` | Algsuperdiff.Section3.Observable.cutoffHomogenizationError_nonneg |  |  |
| `EXT-Algsuperdiff-Section3-Observable-measurable-cutoffHomogenizationError` | Algsuperdiff.Section3.Observable.measurable_cutoffHomogenizationError |  |  |
| `EXT-Algsuperdiff-Section3-Probability-IsTwoTermBigOWith` | Algsuperdiff.Section3.Probability.IsTwoTermBigOWith |  |  |
| `EXT-Algsuperdiff-Section3-Provider-Annealed-coefficientCutoffLaw-exists-annealedBloc` | Algsuperdiff.Section3.Provider.Annealed.coefficientCutoffLaw_exists_annealedBlockMatrixAtScale_eq_blockDiag_smul_one |  |  |
| `EXT-Algsuperdiff-Section3-Provider-Diffusivity-ApproximateRecurrence-blockMatLoewner` | Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.blockMatLoewnerLE_annealedBlockMatrixAtScale_annealedLimit |  |  |
| `EXT-Homogenization-Book-Ch02-doubledResponseJ-eq-half-responseJ-adjoint-sum` | Homogenization.Book.Ch02.doubledResponseJ_eq_half_responseJ_adjoint_sum |  |  |
| `EXT-Homogenization-Book-Ch02-responseMagicIdentitiesTheory` | Homogenization.Book.Ch02.responseMagicIdentitiesTheory |  |  |
| `EXT-Homogenization-Book-Ch02-vecNormSq-averageGradient-le-matrixNorm-sigmaStarInvCoa` | Homogenization.Book.Ch02.vecNormSq_averageGradient_le_matrixNorm_sigmaStarInvCoarse_mul_variationEnergyValue |  |  |
| `EXT-Homogenization-IndependentSums-IsBigOWith-mono-scale` | Homogenization.IndependentSums.IsBigOWith.mono_scale |  |  |
| `EXT-Homogenization-IndependentSums-gammaSigma` | Homogenization.IndependentSums.gammaSigma |  |  |
| `EXT-Homogenization-Internal-Ch02-BookCh02-book-coarseBlockMatrix-eq-old-coarseBlockM` | Homogenization.Internal.Ch02.BookCh02.book_coarseBlockMatrix_eq_old_coarseBlockMatrix_of_data |  |  |
| `EXT-Homogenization-Internal-Ch02-BookCh02-exists-oldCanonicalMatrixData-of-isOpenBou` | Homogenization.Internal.Ch02.BookCh02.exists_oldCanonicalMatrixData_of_isOpenBoundedConvexDomain |  |  |
| `EXT-Homogenization-MuHilbertRealization-minimizerMap-firstVariation` | Homogenization.MuHilbertRealization.minimizerMap_firstVariation |  |  |
| `EXT-Homogenization-blockMatrixOfCoeff` | Homogenization.blockMatrixOfCoeff |  |  |
| `EXT-Homogenization-blockMatrixOfCoeff-matTranspose` | Homogenization.blockMatrixOfCoeff_matTranspose |  |  |
| `EXT-Homogenization-coarseBlockMatrix` | Homogenization.coarseBlockMatrix |  |  |
| `EXT-Homogenization-coarseBlockMatrix-adjointCoeffField-of-exists` | Homogenization.coarseBlockMatrix_adjointCoeffField_of_exists |  |  |
| `EXT-Homogenization-coarseBlockMatrix-subadditive-openCubeSet-descendantsAtDepth-in-l` | Homogenization.coarseBlockMatrix_subadditive_openCubeSet_descendantsAtDepth_in_loewner_order_of_responseJ_blockQuadratic |  |  |
| `EXT-Homogenization-coarseBlockMatrix-translateSet-eq-translateCoeffField` | Homogenization.coarseBlockMatrix_translateSet_eq_translateCoeffField |  |  |
| `EXT-Homogenization-coarseStarredBlockMatrixInv-eq-blockReflect` | Homogenization.coarseStarredBlockMatrixInv_eq_blockReflect |  |  |
| `EXT-Homogenization-cubeSet` | Homogenization.cubeSet |  |  |
| `EXT-Homogenization-isCoarseBlockMatrix-translateSet-iff` | Homogenization.isCoarseBlockMatrix_translateSet_iff |  |  |
| `EXT-Homogenization-isUnit-det-of-isSigmaStarCoarse-of-isEllipticFieldOn-of-isOpenBou` | Homogenization.isUnit_det_of_isSigmaStarCoarse_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain |  |  |
| `EXT-Homogenization-mu-eq-half-coarseBlockMatrix-cube` | Homogenization.mu_eq_half_coarseBlockMatrix_cube |  |  |
| `EXT-Homogenization-openCubeSet` | Homogenization.openCubeSet |  |  |
| `EXT-Homogenization-responseJ-subadditive-openCubeSet-childCubes-of-isEllipticFieldOn` | Homogenization.responseJ_subadditive_openCubeSet_childCubes_of_isEllipticFieldOn |  |  |
| `EXT-Homogenization-sigmaStarInvCoarse-posDef-of-isEllipticFieldOn-of-isOpenBoundedCo` | Homogenization.sigmaStarInvCoarse_posDef_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain |  |  |
| `EXT-InnerProductSpace-toDual` | InnerProductSpace.toDual |  |  |
| `EXT-Matrix-IsHermitian-spectral-theorem` | Matrix.IsHermitian.spectral_theorem |  |  |
| `EXT-Orthonormal-sum-inner-products-le` | Orthonormal.sum_inner_products_le |  |  |
| `EXT-ProbabilityTheory-gaussianReal` | ProbabilityTheory.gaussianReal |  |  |
