module

public import ASDExplicitGamma.Inverse.RawTraceHistory
public import ASDExplicitGamma.Inverse.RawWeakHistory
public import ASDExplicitGamma.Inverse.SourceInterfaceTransport
public import ASDExplicitGamma.Native.OldSignedCellPotentials
public import ASDExplicitGamma.Native.OldSignedErrorProfiles
public import ASDExplicitGamma.Native.OldSignedParentWeakBudgets
public import ASDExplicitGamma.Native.SourceSmallerGammaInterface

/-! The actual paired source observables for the OLD-frame mixed bridge.
These are sample-path definitions, not assumed row bounds. -/
@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Cold ASDExplicitGamma.Gaussian ASDExplicitGamma.Native
  ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational
open scoped BigOperators

noncomputable section

/-- The actual partially inserted scalar response coefficient on the
completed source cube `Q_m`, represented on its closed response domain. -/
noncomputable def mixedBridgeResponseCoefficient (m : ℤ)
    (t : ℝ) (ω : Cutoff.CutoffSample 2) :
    ResponseCoefficient (openCubeSet (originCube 2 m)) := by
  let Q := originCube 2 m
  let K := closure (cubeSet Q)
  letI : CompactSpace K := isCompact_iff_compactSpace.mp (isBounded_cubeSet Q).isCompact_closure
  letI : CompactSpace (closure (openCubeSet Q)) :=
    isCompact_iff_compactSpace.mp (isBounded_openCubeSet Q).isCompact_closure
  let incl : C(closure (openCubeSet Q), K) :=
    ⟨fun x => ⟨x.1, closure_mono (openCubeSet_subset_cubeSet Q) x.2⟩,
      continuous_subtype_val.subtype_mk _⟩
  exact BoundedContinuousFunction.mkOfCompact
    ((modelInsertedScalar K m t ω).comp incl)

/-- All actual source roots inside the observer `Q_(m+40)`, with the six
source offsets `r₀=0,…,5` and their full `9^(40+r₀)` descendant populations. -/
def mixedBridgeObserverSourceRoots (m : ℤ) : Finset (TriadicCube 2) :=
  (Finset.range 6).biUnion fun r =>
    descendantsAtDepth (originCube 2 (m + 40)) (40 + r)

/-- The actual complete-history inverse profile of one observer source root,
in the fixed OLD true frame and partially inserted coefficient. -/
noncomputable def mixedBridgeRootHistoryProfile (M : ABKModel 2) (m : ℤ)
    (t : ℝ) (ω : Cutoff.CutoffSample 2) (Q : TriadicCube 2) : ℝ :=
  (Annealed.sigmaBar M m : ℝ) * lemmaVInverseHistory Q
    (Model.partialInsertedCoefficient M m t ω).toFun ((3 : ℝ) ^ (1 / 4 : ℝ))

/-- The single intrinsic global inverse maximum over exactly the observer
source-root population, in the actual partially inserted coefficient and
fixed OLD true frame. -/
noncomputable def mixedBridgeBstar (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  Book.Ch02.finsetSupReal (mixedBridgeObserverSourceRoots m)
    (mixedBridgeRootHistoryProfile M m t ω)

theorem mixedBridgeBstar_eq_raw_history_max (M : ABKModel 2) (m : ℤ)
    (t : ℝ) (ω : Cutoff.CutoffSample 2) :
    mixedBridgeBstar M m t ω = rawFiniteInverseHistoryMax
      (mixedBridgeObserverSourceRoots m)
      (Model.partialInsertedCoefficient M m t ω).toFun (Annealed.sigmaBar M m : ℝ) := by
  unfold mixedBridgeBstar mixedBridgeRootHistoryProfile rawFiniteInverseHistoryMax
  rfl

/-- OLD local inverse baseline at weak depth `j`. -/
def mixedBridgeOldInverseBaseline (M : ABKModel 2) (j : ℕ) : ℝ :=
  (3683 / 2500 : ℝ) * (3 : ℝ) ^ (2 * M.gamma * (j : ℝ))

/-- The positive excess of the actual OLD depth inverse maximum above its
source baseline; the max makes this the exact positive split remainder. -/
noncomputable def mixedBridgeOldDepthRemainder (M : ABKModel 2) (m : ℤ)
    (t : ℝ) (ω : Cutoff.CutoffSample 2) (j : ℕ) : ℝ :=
  max 0
    (rawFiniteInverseDepthMax (mixedBridgeObserverSourceRoots m)
      (Model.partialInsertedCoefficient M m t ω).toFun
      (Annealed.sigmaBar M m : ℝ) j - mixedBridgeOldInverseBaseline M j)

/-- The actual four-load weak trace average `T̄_j` on the common descendant
partition of the completed source cube `Q_m`. -/
noncomputable def mixedBridgeTbar (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) (j : ℕ) : ℝ :=
  rawWeakTraceSequence M m (originCube 2 m) t ω j

/-- The weak history of the actual source traces, with its unsquared
quarter-discount chronology. -/
noncomputable def mixedBridgeHbar (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  rawWeakTraceHistory (mixedBridgeTbar M m t ω)

/-- The OLD chronology proxy `Theta_o(t)`, with its original source split and
actual trace averages retained at every weak depth. -/
noncomputable def mixedBridgeThetaOld (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  ∑' j : ℕ,
    (1 - Scalar.inverseHistoryDiscount ^ 2) *
      Scalar.inverseHistoryDiscount ^ (2 * j) *
      (mixedBridgeOldInverseBaseline M j +
        mixedBridgeOldDepthRemainder M m t ω j) *
      mixedBridgeTbar M m t ω j

/-- The four-load parent primal projection budget at depth `j`, on `Q_m` and
in the true OLD frame. Its complete weighted sum is `V²`. -/
noncomputable def mixedBridgeVDepthSq (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) (j : ℕ) : ℝ := by
  let Q := originCube 2 m
  let k := mixedBridgeResponseCoefficient m t ω
  let σ : ℝ := Annealed.sigmaBar M m
  let hσ : 0 < σ := (Annealed.sigmaBar_characterization M m).1
  exact ∑ c : BlockCoord 2,
    oldSignedPrimalProjectionEnergy Q j M.nu σ M.nu_pos hσ k (blockBasis c)

/-- The complete weighted primal source square `V²`. -/
noncomputable def mixedBridgeV2 (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  let Q := originCube 2 m
  let k := mixedBridgeResponseCoefficient m t ω
  let σ : ℝ := Annealed.sigmaBar M m
  oldSignedPrimalErrorSize Q Q M.nu σ M.nu_pos
    (Annealed.sigmaBar_characterization M m).1 k ^ 2

/-- The complete weighted reciprocal source square `G²`. -/
noncomputable def mixedBridge (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  let Q := originCube 2 m
  let k := mixedBridgeResponseCoefficient m t ω
  let σ : ℝ := Annealed.sigmaBar M m
  oldSignedReciprocalErrorSize Q Q M.nu σ M.nu_pos
    (Annealed.sigmaBar_characterization M m).1 k ^ 2

/-- The paired source sizes used by the bridge, with squares defined by the
complete weighted weak-depth sums above. -/
noncomputable def mixedBridgeV (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) : ℝ := Real.sqrt (mixedBridgeV2 M m t ω)

noncomputable def mixedBridgeG (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) : ℝ := Real.sqrt (mixedBridge M m t ω)

/-- At one actual descendant, the sum of weak squares of its four local
first-corrector gradients from the true parent minimizers. -/
noncomputable def mixedBridgeLocalCorrectorSq (M : ABKModel 2) (m : ℤ)
    (t : ℝ) (ω : Cutoff.CutoffSample 2) (j : ℕ)
    (C : SquareCells (originCube 2 m) j) : ℝ := by
  let Q := originCube 2 m
  let U := C.val
  let hU : openCubeSet U ⊆ openCubeSet Q :=
    openCubeSet_subset_of_mem_descendantsAtDepth C.property
  let k := mixedBridgeResponseCoefficient m t ω
  let σ : ℝ := Annealed.sigmaBar M m
  let hσ : 0 < σ := (Annealed.sigmaBar_characterization M m).1
  exact ∑ a : BlockCoord 2,
    vectorWeakHaarNorm U (fun x =>
      (oldSignedCellFirstCorrector Q U hU M.nu σ M.nu_pos hσ k
        (oldSignedFrameCanonicalField Q M.nu σ M.nu_pos hσ k (blockBasis a))
        (Lp.memLp (oldSignedFrameCanonicalField Q M.nu σ M.nu_pos hσ k (blockBasis a)))).toH1Function.grad x) ^ 2

/-- The actual local first-corrector weak energy at depth `j`, averaged over
its complete descendant tiling. -/
noncomputable def mixedBridgeVLocalDepthSq (M : ABKModel 2) (m : ℤ)
    (t : ℝ) (ω : Cutoff.CutoffSample 2) (j : ℕ) : ℝ :=
  squareCellMean (originCube 2 m) j (mixedBridgeLocalCorrectorSq M m t ω j)

/-- `V_l²`: the complete weighted source sum of actual local first-corrector
weak norms. -/
noncomputable def mixedBridgeVl2 (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  ∑' j : ℕ,
    (1 - Scalar.inverseHistoryDiscount ^ 2) *
      Scalar.inverseHistoryDiscount ^ (2 * j) * mixedBridgeVLocalDepthSq M m t ω j

/-- The actual local first-corrector source size `V_l`, whose square is the
complete weighted weak-depth energy above. -/
noncomputable def mixedBridgeVl (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) : ℝ := Real.sqrt (mixedBridgeVl2 M m t ω)

/-- The completed-prefix `xi_5` cap supplied by the actual source-row
interface. -/
def mixedBridgeXiPre (M : ABKModel 2) : ℝ :=
  theta M * (inSourceXi5Pre : ℝ)

/-- The full deterministic reserve for the mixed expansion. -/
def mixedBridgeReserve (M : ABKModel 2) : ℝ :=
  (1 / 10 ^ 12 : ℝ) * theta M

/-- The original OLD source-mean slope summed with its chronology weights. -/
noncomputable def mixedBridgeXiSlope (M : ABKModel 2) (h : ℝ) (m : ℤ) : ℝ :=
  ∑' j : ℕ,
    (1 - Scalar.inverseHistoryDiscount ^ 2) *
      Scalar.inverseHistoryDiscount ^ (2 * j) *
      mixedBridgeOldInverseBaseline M j * inSourceMeanSlopeActual M h m j

/-- The deterministic source chronology budget at insertion time `t`. -/
noncomputable def mixedBridgeXi (M : ABKModel 2) (h : ℝ) (m : ℤ)
    (t : ℝ) : ℝ :=
  mixedBridgeXiPre M + mixedBridgeReserve M + t * mixedBridgeXiSlope M h m

/-- The actual reference trace whose expectation is `f` in the parent-gap row. -/
noncomputable def mixedBridgeAnchorTrace (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  rawCubeFourLoadTrace M m (originCube 2 m) t ω

/-- The reference mean `f = E[T(Q_m; a_t, sigmaBar M m)]` in the cutoff law. -/
noncomputable def mixedBridgeAnchorMean (M : ABKModel 2) (m : ℤ) (t : ℝ) : ℝ :=
  ∫ ω, mixedBridgeAnchorTrace M m t ω ∂(Cutoff.cutoffSampleLaw M).toMeasure

/-- The sample-path mixed moment integrand `B*^k Theta_o` for `k≤3`. -/
noncomputable def mixedBridgeBstarThetaIntegrand (M : ABKModel 2) (m : ℤ)
    (t : ℝ) (k : ℕ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  mixedBridgeBstar M m t ω ^ k * mixedBridgeThetaOld M m t ω

/-- The sample-path mixed moment integrand `B*^k V²`. -/
noncomputable def mixedBridgeBstarVIntegrand (M : ABKModel 2) (m : ℤ)
    (t : ℝ) (k : ℕ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  mixedBridgeBstar M m t ω ^ k * mixedBridgeV2 M m t ω

/-- The sample-path mixed moment integrand `B*^k (V²+G²)`. -/
noncomputable def mixedBridgeBstarPairIntegrand (M : ABKModel 2) (m : ℤ)
    (t : ℝ) (k : ℕ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  mixedBridgeBstar M m t ω ^ k *
    (mixedBridgeV2 M m t ω + mixedBridge M m t ω)

/-- The sample-path first-corrector mixed moment integrand `B* V_l²`. -/
noncomputable def mixedBridgeBstarVlIntegrand (M : ABKModel 2) (m : ℤ)
    (t : ℝ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  mixedBridgeBstar M m t ω * mixedBridgeVl2 M m t ω

/-- The actual expectation `E[(B*)^k Theta_o]` under the partial-insertion
cutoff law. -/
noncomputable def mixedBridgeBstarThetaMoment (M : ABKModel 2) (m : ℤ)
    (t : ℝ) (k : ℕ) : ℝ :=
  ∫ ω, mixedBridgeBstarThetaIntegrand M m t k ω
    ∂(Cutoff.cutoffSampleLaw M).toMeasure

/-- The actual expectation `E[(B*)^k V²]` under the same law. -/
noncomputable def mixedBridgeBstarVMoment (M : ABKModel 2) (m : ℤ)
    (t : ℝ) (k : ℕ) : ℝ :=
  ∫ ω, mixedBridgeBstarVIntegrand M m t k ω
    ∂(Cutoff.cutoffSampleLaw M).toMeasure

/-- The actual expectation `E[(B*)^k (V²+G²)]` under the same law. -/
noncomputable def mixedBridgeBstarPairMoment (M : ABKModel 2) (m : ℤ)
    (t : ℝ) (k : ℕ) : ℝ :=
  ∫ ω, mixedBridgeBstarPairIntegrand M m t k ω
    ∂(Cutoff.cutoffSampleLaw M).toMeasure

/-- The actual expectation `E[B* V_l²]` under the same law. -/
noncomputable def mixedBridgeBstarVlMoment (M : ABKModel 2) (m : ℤ)
    (t : ℝ) : ℝ :=
  ∫ ω, mixedBridgeBstarVlIntegrand M m t ω
    ∂(Cutoff.cutoffSampleLaw M).toMeasure

end
end ASDExplicitGamma.Inverse
