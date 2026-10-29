module

public import ASDExplicitGamma.Main.ThetaGeneratorHotGeneratorPathwise
public import ASDExplicitGamma.Main.HotGeneratorIntegral
public import ASDExplicitGamma.Main.ThetaGeneratorHotObsVl2
public import ASDExplicitGamma.Main.ThetaGeneratorHotRemainderFeedbackMoments
public import ASDExplicitGamma.Main.ThetaGeneratorHotFeedbackPathwise
public import ASDExplicitGamma.Main.ThetaGeneratorHotEOscillationPointwise
public import ASDExplicitGamma.Main.ThetaGeneratorHotObsSplit
public import ASDExplicitGamma.Main.ThetaGeneratorHotTrialExpectationsSplit
public import ASDExplicitGamma.Main.ThetaGeneratorHotObsDrop
public import ASDExplicitGamma.Main.ThetaGeneratorMixedBridgeLocalCore
public import ASDExplicitGamma.Main.ThetaGeneratorEnvelopeA
public import ASDExplicitGamma.Main.LoadsAndSlopes
public import ASDExplicitGamma.Main.SourcePrefixGates
public import ASDExplicitGamma.Native.SourceRowsInterface
public import ASDExplicitGamma.Inverse.SourceInterfaceRows
public import ASDExplicitGamma.Scalar.MixedSourceCarriers
public import ASDExplicitGamma.Inverse.MixedBridgeConclusion
public import ASDExplicitGamma.Inverse.MixedBridgeLocalTheta
public import ASDExplicitGamma.Inverse.MixedBridgeLocalWeightedTheta
public import ASDExplicitGamma.Inverse.MixedBridgeSharpSlope
public import ASDExplicitGamma.Numerics.Native.Source5
public import ASDExplicitGamma.Main.AffineObserverFrame
public import ASDExplicitGamma.Inverse.MixedBridgeLocalCorrector
public import ASDExplicitGamma.Inverse.ParentGapRare
public import ASDExplicitGamma.Inverse.RawTraceHistory
public import ASDExplicitGamma.Native.OldSignedParentWeakBudgets
public import ASDExplicitGamma.Native.OldSignedSourceInverseSplit
public import ASDExplicitGamma.Main.ThetaGeneratorHotESourceSquareNode
public import ASDExplicitGamma.Main.ThetaGeneratorHotEOscillationNode
public import ASDExplicitGamma.Main.ThetaGeneratorHotRemainderFeedbackNode
public import ASDExplicitGamma.Main.AffineObserverIntegrable
public import ASDExplicitGamma.Main.GeneratorErrorInventoryAssembly
public import ASDExplicitGamma.Main.ThetaGeneratorELinearObsSplit
public import ASDExplicitGamma.Main.ThetaGeneratorELinearObsMeanAmplitude
public import ASDExplicitGamma.Main.ThetaGeneratorELinearCellExpectation
public import ASDExplicitGamma.Main.ELinearCauchy
public import ASDExplicitGamma.Main.ELinearFlatCaps
public import ASDExplicitGamma.Main.EOscillationFlatOscillationCaps
public import ASDExplicitGamma.Native.OldSignedCenteredPositive
public import ASDExplicitGamma.Main.EOscillationCellScale
public import ASDExplicitGamma.Main.AffineFlatBoundary
public import ASDExplicitGamma.Main.ThetaGeneratorELinearObsGPart
public import ASDExplicitGamma.Main.ThetaGeneratorEParentGapActualLaw
public import ASDExplicitGamma.Main.ThetaGeneratorEBottomCovarianceActualLaw
public import ASDExplicitGamma.Main.ThetaGeneratorHotCovNodeFinal
public import ASDExplicitGamma.Main.ThetaGeneratorAffine

/-! Generator assembly, step 4: the integrated generator bound at the observer root in
the `_of_inverse_deficit` form. The inverse-deficit input is the explicit bound on the mean of
the actual trace term `-b² (tr D - 2)` of the bottom covariance row. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse
  ASDExplicitGamma.Model ASDExplicitGamma.Native ASDExplicitGamma.Response
  ASDExplicitGamma.Triadic ASDExplicitGamma.Scalar
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff

noncomputable section

/-- The stationary affine term of the generator inequality (MA-AFFINE). -/
def mainAffineTerm_Th (M : ABKModel 2) (b q t : ℝ) : ℝ :=
  (b ^ 2 / 2) * mainEnvelopeA (b ^ 2) M.gamma (theta M * mainSourceMeanPrefix) t +
    (b ^ 2 * q) * (mainBeta - 1) + (4 + 2 * Real.sqrt 2) * (31.2 : ℝ) * mainA2 (b ^ 2) / 9

/-- Integral of a left-associated sum of ten integrable functions. -/
theorem hotGen_integral_sum10_Th {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 : Ω → ℝ}
    (h1 : Integrable f1 μ) (h2 : Integrable f2 μ) (h3 : Integrable f3 μ)
    (h4 : Integrable f4 μ) (h5 : Integrable f5 μ) (h6 : Integrable f6 μ)
    (h7 : Integrable f7 μ) (h8 : Integrable f8 μ) (h9 : Integrable f9 μ)
    (h10 : Integrable f10 μ) :
    (∫ ω, (f1 ω + f2 ω + f3 ω + f4 ω + f5 ω + f6 ω + f7 ω + f8 ω + f9 ω + f10 ω) ∂μ) =
      (∫ ω, f1 ω ∂μ) + (∫ ω, f2 ω ∂μ) + (∫ ω, f3 ω ∂μ) + (∫ ω, f4 ω ∂μ) + (∫ ω, f5 ω ∂μ) +
        (∫ ω, f6 ω ∂μ) + (∫ ω, f7 ω ∂μ) + (∫ ω, f8 ω ∂μ) + (∫ ω, f9 ω ∂μ) +
        ∫ ω, f10 ω ∂μ := by
  have i2 : Integrable (fun ω => f1 ω + f2 ω) μ := h1.add h2
  have i3 : Integrable (fun ω => f1 ω + f2 ω + f3 ω) μ := i2.add h3
  have i4 : Integrable (fun ω => f1 ω + f2 ω + f3 ω + f4 ω) μ := i3.add h4
  have i5 : Integrable (fun ω => f1 ω + f2 ω + f3 ω + f4 ω + f5 ω) μ := i4.add h5
  have i6 : Integrable (fun ω => f1 ω + f2 ω + f3 ω + f4 ω + f5 ω + f6 ω) μ := i5.add h6
  have i7 : Integrable (fun ω => f1 ω + f2 ω + f3 ω + f4 ω + f5 ω + f6 ω + f7 ω) μ := i6.add h7
  have i8 : Integrable (fun ω => f1 ω + f2 ω + f3 ω + f4 ω + f5 ω + f6 ω + f7 ω + f8 ω) μ :=
    i7.add h8
  have i9 : Integrable (fun ω => f1 ω + f2 ω + f3 ω + f4 ω + f5 ω + f6 ω + f7 ω + f8 ω + f9 ω) μ :=
    i8.add h9
  rw [integral_add i9 h10, integral_add i8 h9, integral_add i7 h8, integral_add i6 h7,
    integral_add i5 h6, integral_add i4 h5, integral_add i3 h4, integral_add i2 h3,
    integral_add h1 h2]

/-- Integration of the pathwise generator bound against the ten integrable pieces. -/
theorem hotGen_combine_Th {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F Lg Aff Gs Gc Go Gf Gt Gb τ : Ω → ℝ} (Bn c : ℝ)
    (hF : Integrable F μ) (hLg : Integrable Lg μ) (hAff : Integrable Aff μ)
    (hGs : Integrable Gs μ) (hGc : Integrable Gc μ) (hGo : Integrable Go μ)
    (hGf : Integrable Gf μ) (hGt : Integrable Gt μ) (hGb : Integrable Gb μ)
    (hτ : Integrable τ μ)
    (hae : ∀ᵐ ω ∂μ, F ω ≤ Lg ω + Bn + Aff ω + Gs ω + Gc ω + Go ω + Gf ω + Gt ω +
      (-c * (τ ω - 2)) + Gb ω) :
    (∫ ω, F ω ∂μ) ≤ (∫ ω, Lg ω ∂μ) + Bn + (∫ ω, Aff ω ∂μ) + (∫ ω, Gs ω ∂μ) +
      (∫ ω, Gc ω ∂μ) + (∫ ω, Go ω ∂μ) + (∫ ω, Gf ω ∂μ) + (∫ ω, Gt ω ∂μ) +
      (-c * ((∫ ω, τ ω ∂μ) - 2)) + ∫ ω, Gb ω ∂μ := by
  have hT : Integrable (fun ω => -c * (τ ω - 2)) μ :=
    (hτ.sub (integrable_const (2 : ℝ))).const_mul (-c)
  have hB : Integrable (fun _ : Ω => Bn) μ := integrable_const Bn
  have hsum := hotGen_integral_sum10_Th hLg hB hAff hGs hGc hGo hGf hGt hT hGb
  have hint : Integrable (fun ω => Lg ω + Bn + Aff ω + Gs ω + Gc ω + Go ω + Gf ω + Gt ω +
      (-c * (τ ω - 2)) + Gb ω) μ :=
    (((((((((hLg.add hB).add hAff).add hGs).add hGc).add hGo).add hGf).add hGt).add hT).add hGb)
  have hmono := integral_mono_ae hF hint hae
  refine hmono.trans (le_of_eq ?_)
  rw [hsum, integral_const, integral_const_mul, integral_sub hτ (integrable_const _),
    integral_const]
  simp

/-- The actual inverse-trace term `tr D` of the bottom covariance row on the observer root. -/
def hotInverseTrace_Th (M : ABKModel 2) (m : ℤ) (hobs : ℕ) (t : ℝ) (ω : CutoffSample 2) : ℝ :=
  Matrix.trace (coarseBlockMatrix (openCubeSet (originCube 2 (m + (hobs : ℤ))))
    (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
      (mainELinearObsCoefficient (originCube 2 (m + (hobs : ℤ))) m t ω))).lowerRight

end

end ASDExplicitGamma.Main
