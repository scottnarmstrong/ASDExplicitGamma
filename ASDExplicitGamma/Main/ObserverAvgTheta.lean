module

public import ASDExplicitGamma.Main.EnvelopeA
public import ASDExplicitGamma.Main.LoadsAndSlopes
public import ASDExplicitGamma.Native.SourceRowsInterface
public import ASDExplicitGamma.Inverse.SourceInterfaceRows
public import ASDExplicitGamma.Scalar.MixedSourceCarriers
public import ASDExplicitGamma.Inverse.MixedBridgeConclusion
public import ASDExplicitGamma.Inverse.MixedBridgeLocalTheta
public import ASDExplicitGamma.Inverse.MixedBridgeLocalWeightedTheta
public import ASDExplicitGamma.Inverse.MixedBridgeSharpSlope
public import ASDExplicitGamma.Main.SourcePrefixGates
public import ASDExplicitGamma.Numerics.Native.Source5
public import ASDExplicitGamma.Main.ObserverParentGapExpectation
public import ASDExplicitGamma.Inverse.MixedBridgeObsCellTheta
public import ASDExplicitGamma.Main.ELinearCellExpectation

/-! Observer-root parent-gap row: expectation of the reference-subtracted tiled
parent primal error, `E avg Theta <= xi`. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open MeasureTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Model
  ASDExplicitGamma.Native
open ASDExplicitGamma.Numerics.MainReturn ASDExplicitGamma.Numerics.Native
  ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
open Algsuperdiff.Section3.Cutoff ASDExplicitGamma.Response ASDExplicitGamma.Variational
open scoped ENNReal
open ASDExplicitGamma.Numerics.MainReturn ASDExplicitGamma.Numerics.Native
  ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
open Algsuperdiff.Section3.Cutoff ASDExplicitGamma.Response ASDExplicitGamma.Variational
open scoped ENNReal
attribute [local irreducible] Homogenization.descendantsAtDepth



/-- Average of the local OLD-Theta carriers over the observer tiling: integrable
with mean at most `xi`, and it majorizes the paired parent error average. -/
theorem observer_avg_theta_row
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hobs : ℕ) (h40 : hobs ≤ 40) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    Integrable (fun ω => descendantsAverage (originCube 2 (m + hobs)) (5 + hobs)
        (fun U => mixedOldTheta M m U t ω)) μ ∧
      (∫ ω, descendantsAverage (originCube 2 (m + hobs)) (5 + hobs)
        (fun U => mixedOldTheta M m U t ω) ∂μ) ≤
        mainEnvelopeXi ((q3ModelAmplitude M h (m + 1) /
          (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma mainSourceInversePrefix (theta M) t := by
  intro μ
  classical
  set Q : TriadicCube 2 := originCube 2 (m + hobs) with hQ
  set d : ℕ := 5 + hobs with hd
  set ξ : ℝ := mainEnvelopeXi ((q3ModelAmplitude M h (m + 1) /
    (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma mainSourceInversePrefix (theta M) t with hξ
  have hrow := fun U (hU : U ∈ descendantsAtDepth Q d) =>
    main_envelope_xi_obscell_row M h hM hγ N hpast m hm t ht U
      (observer_cell_scale m hobs U hU)
  have hΘint : Integrable (fun ω => descendantsAverage Q d
      (fun U => mixedOldTheta M m U t ω)) μ := by
    unfold descendantsAverage
    exact (integrable_finsetSum _ (fun U hU => (hrow U hU).1)).const_mul _
  refine ⟨hΘint, ?_⟩
  have hcardpos : 0 < ((descendantsAtDepth Q d).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (descendantsAtDepth_nonempty Q d)
  have h1 : (∫ ω, descendantsAverage Q d (fun U => mixedOldTheta M m U t ω) ∂μ) =
      ((descendantsAtDepth Q d).card : ℝ)⁻¹ *
        ∑ U ∈ descendantsAtDepth Q d, ∫ ω, mixedOldTheta M m U t ω ∂μ := by
    unfold descendantsAverage
    rw [integral_const_mul, integral_finsetSum _ (fun U hU => (hrow U hU).1)]
  rw [h1]
  have h2 : (∑ U ∈ descendantsAtDepth Q d, ∫ ω, mixedOldTheta M m U t ω ∂μ) ≤
      ∑ U ∈ descendantsAtDepth Q d, ξ :=
    Finset.sum_le_sum (fun U hU => (hrow U hU).2)
  rw [Finset.sum_const, nsmul_eq_mul] at h2
  calc _ ≤ ((descendantsAtDepth Q d).card : ℝ)⁻¹ *
        (((descendantsAtDepth Q d).card : ℝ) * ξ) :=
        mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr hcardpos.le)
    _ = ξ := by field_simp

end ASDExplicitGamma.Main
