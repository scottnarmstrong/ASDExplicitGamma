module

public import ASDExplicitGamma.Inverse.RawTraceHistory
public import ASDExplicitGamma.Inverse.BankDepthBlocks
public import ASDExplicitGamma.Inverse.BankObservers
public import ASDExplicitGamma.Inverse.BankDepthObservers
public import ASDExplicitGamma.Inverse.SourceInterfaceEnergy
public import ASDExplicitGamma.Inverse.SourceInterfaceRows
public import ASDExplicitGamma.Main.MixedBridge

/-! Source-bound carriers for the mixed bridge. These definitions fix the
actual OLD-frame trace, global observer maximum, local depth remainder,
depth-average trace, source-row input, and OLD source-energy slope. They do
not assert the missing paired `V`, `G`, or local-corrector estimates. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Inverse ASDExplicitGamma.Main
open ASDExplicitGamma.Native ASDExplicitGamma.Gaussian
open scoped ENNReal

noncomputable section

/-- The actual global observer roots for the five-level mixed bridge. -/
def mixedObserverRoots (m : ℤ) : Finset (TriadicCube 2) :=
  bankObserverRootUnion (originCube 2 (m + 40)) 5

/-- The actual complete global inverse-history maximum at insertion time `t`.
Its real representative is finite almost everywhere by the global bank. -/
def mixedGlobalHistoryMax (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  (bankFiniteRootHistoryMax (mixedObserverRoots m) M m (m + 40)
    (bankPartialInsertionWeights m 1 t) ω).toReal

/-- The actual source four-load trace at the old scale, evaluated on the
partial-insertion coefficient and in the fixed completed frame. -/
def mixedOldFrameTrace (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  rawDepthFourLoadTrace M m m t ω

/-- The actual depth-`j` four-load trace average on an explicit source cube. -/
def mixedDepthTraceAverage (M : ABKModel 2) (m : ℤ)
    (Q : TriadicCube 2) (t : ℝ) (ω : Cutoff.CutoffSample 2) (j : ℕ) : ℝ :=
  rawWeakTraceSequence M m Q t ω j

/-- The actual local-bank depth-`j` rare remainder over the full observer-root
union, with the same partial insertion as the global bank. -/
def mixedOldLocalDepthRemainder (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (j : ℕ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  inverseBankDepthBlockRemainder .localInverse
    (bankObserverDepthRootUnion (originCube 2 (m + 40)) 5 j)
    M m (m + 40) (bankPartialInsertionWeights m 1 t) j ω

/-- The exact OLD local inverse-bank term paired with the depth-`j` source
trace in `Theta_o`. -/
def mixedOldDepthCoefficient (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (j : ℕ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  (inverseBankCap .localInverse : ℝ) * bankDepthFrame M j +
    mixedOldLocalDepthRemainder M m t j ω

/-- The deterministic component of the OLD depth coefficient is exactly the
source local cap `b_o 3^(2 gamma j)`. -/
theorem mixed_old_depth_coefficient_formula
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (j : ℕ)
    (ω : Cutoff.CutoffSample 2) :
    mixedOldDepthCoefficient M m t j ω =
      (3683 / 2500 : ℝ) * (3 : ℝ) ^ (2 * M.gamma * (j : ℝ)) +
        mixedOldLocalDepthRemainder M m t j ω := by
  simp [mixedOldDepthCoefficient, inverseBankCap, bankDepthFrame]

/-- One term in the exact OLD-bank weighted weak-trace proxy. The source cube
is explicit so the paired four-load assembly can select the audited root. -/
def mixedOldThetaTerm (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (t : ℝ) (j : ℕ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  (1 - inverseHistoryDiscount ^ 2) * inverseHistoryDiscount ^ (2 * j) *
    mixedOldDepthCoefficient M m t j ω *
      mixedDepthTraceAverage M m Q t ω j

/-- The `Theta_o` carrier formed from the actual local depth bank and actual
depth-average trace. Summability is supplied by the mixed-bridge producer. -/
def mixedOldTheta (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (t : ℝ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  ∑' j : ℕ, mixedOldThetaTerm M m Q t j ω

/-- The certified smaller-gamma cap for the depth-five source row. -/
def mixedXiPreCap (M : ABKModel 2) : ℝ :=
  theta M * (inSourceXi5Pre : ℝ)

/-- The certified depth-five weak source row is bounded by its exact carried
smaller-gamma cap. -/
theorem mixed_xi_pre_cap_of_smaller_gamma
    (M : ABKModel 2) (m : ℤ)
    (hSmall : NativeSourceSmallerGammaBounds M m) :
    nativeCompletedSourceWeak M m 5 ≤ ENNReal.ofReal (mixedXiPreCap M) := by
  simpa [mixedXiPreCap] using
    (in_source_rows_source M m hSmall).2.2.2.1

/-- The actual OLD source-energy slope series which transports the weak-row
envelope along the insertion path. -/
def mixedXiSlope (M : ABKModel 2) (h : ℝ) (m : ℤ) : ℝ :=
  ∑' r : ℕ, inSourceOldEnergyHistoryWeight M r *
    inSourceMeanSlopeActual M h m r

/-- The actual average weak-history carrier in `L²`, with its source
integrability witness kept explicit. -/
def mixedOldWeakHistory (M : ABKModel 2) (m : ℤ)
    (Q : TriadicCube 2) (t : ℝ)
    (hT : ∀ j, MemLp (rawWeakTraceSequence M m Q t · j) 2
      (Cutoff.cutoffSampleLaw M).toMeasure) :
    Lp ℝ 2 (Cutoff.cutoffSampleLaw M).toMeasure :=
  rawWeakTraceHistoryLp M m Q t hT

/-- The carried OLD variance row plus the rare-sum reserve and transported
OLD source-energy slope from the mixed-bridge contract. -/
def mixedXi (M : ABKModel 2) (h : ℝ) (m : ℤ) (t : ℝ) : ℝ :=
  mixedXiPreCap M + (1 / 10^12 : ℝ) * theta M + t * mixedXiSlope M h m

/-- IN-MIXED-BRIDGE's source conclusion at the completed source cube `Q_m`.
The OLD-frame trace, observer maximum, depth-history trace, local-bank Theta,
and xi path are fixed to their source carriers above. The paired `V`, `G`,
and `Vl` carriers remain explicit time-dependent arguments. The `Inverse/BridgeObservables` module gives their
actual definitions there; the final producer must
instantiate these arguments with those definitions and prove the rows. This
contract type does not identify arbitrary arguments with the actual carriers.
The sharp
`xi_{5,pre}` in `mixedXiPreCap` enters `IN-MIXED-BRIDGE` through
`IN-SOURCE-ROWS`: instantiate the `in_source_rows_source` and use its
`nativeCompletedSourceWeak M m 5` estimate. It does not come from the weaker
`NA-SOURCE-ROWS` caps. -/
def InMixedBridgeConclusion
    (M : ABKModel 2) (h : ℝ) (m : ℤ)
    (hTrace : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → ∀ j : ℕ,
      MemLp (rawWeakTraceSequence M m (originCube 2 m) t · j) 2
        (Cutoff.cutoffSampleLaw M).toMeasure)
    (V G Vl : ℝ → Cutoff.CutoffSample 2 → ℝ)
    (H_o : ℝ → ℝ)
    (_hHistory : ∀ t : ℝ, ∀ ht : t ∈ Set.Icc (0 : ℝ) 1,
      ‖mixedOldWeakHistory M m (originCube 2 m) t (hTrace t ht)‖ ≤ H_o t) :
    Prop :=
  ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
    (∀ k : Fin 4,
      (∫ ω, mixedGlobalHistoryMax M m t ω ^ k.val *
        mixedOldTheta M m (originCube 2 m) t ω
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
          mainBeta ^ k.val * mixedXi M h m t) ∧
    (∀ k : Fin 4,
      (∫ ω, mixedGlobalHistoryMax M m t ω ^ k.val * V t ω ^ 2
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
          mainBeta ^ k.val *
            (mixedXi M h m t - mainBetaOld *
              (∫ ω, mixedOldFrameTrace M m t ω
                ∂(Cutoff.cutoffSampleLaw M).toMeasure))) ∧
    (∀ k : Fin 4,
      (∫ ω, mixedGlobalHistoryMax M m t ω ^ k.val *
        (V t ω ^ 2 + G t ω ^ 2)
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
          2 * mainBeta ^ k.val * mixedXi M h m t) ∧
    (∫ ω, mixedGlobalHistoryMax M m t ω * Vl t ω ^ 2
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        mainBeta * mixedXi M h m t +
          mainEpsNew * (1 + inverseHistoryDiscount) * mainBeta *
            H_o t

end

end ASDExplicitGamma.Scalar
