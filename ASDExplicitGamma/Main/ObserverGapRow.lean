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
public import ASDExplicitGamma.Main.ObserverParentGapPaired
public import ASDExplicitGamma.Main.ObserverParentGapExpectation
public import ASDExplicitGamma.Inverse.MixedBridgeObsCellTheta
public import ASDExplicitGamma.Main.ELinearCellExpectation

/-! Observer-root parent-gap row: expectation of the reference-subtracted tiled
parent primal error, `E sqrt(avg G^2) <= sqrt(2 xi)`. -/

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


/-- Observer-root reciprocal (G) row: the tiled parent reciprocal error size has
an integrable majorant with mean at most `sqrt (2 xi)`. The paired majorant
`Pbar >= sqrt (avg (V^2 + G^2))` has mean at most `sqrt (2 xi)` too. -/
theorem observer_parent_gap_G_row
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hobs : ℕ) (h40 : hobs ≤ 40) :
    let μ := (Cutoff.cutoffSampleLaw M).toMeasure
    ∃ Gbar : CutoffSample 2 → ℝ, Integrable Gbar μ ∧ (∀ ω, 0 ≤ Gbar ω) ∧
      (∀ ω, Real.sqrt (descendantsAverage (originCube 2 (m + hobs)) (5 + hobs)
        (fun U => oldSignedReciprocalErrorSize (originCube 2 (m + hobs)) U M.nu
          (Annealed.sigmaBar M m : ℝ) M.nu_pos
          (Annealed.sigmaBar_characterization M m).1
          (mainELinearObsCoefficient (originCube 2 (m + hobs)) m t ω) ^ 2)) ≤
        Gbar ω) ∧
      (∀ ω, Real.sqrt (descendantsAverage (originCube 2 (m + hobs)) (5 + hobs)
        (fun U => oldSignedPrimalErrorSize (originCube 2 (m + hobs)) U M.nu
          (Annealed.sigmaBar M m : ℝ) M.nu_pos
          (Annealed.sigmaBar_characterization M m).1
          (mainELinearObsCoefficient (originCube 2 (m + hobs)) m t ω) ^ 2 +
         oldSignedReciprocalErrorSize (originCube 2 (m + hobs)) U M.nu
          (Annealed.sigmaBar M m : ℝ) M.nu_pos
          (Annealed.sigmaBar_characterization M m).1
          (mainELinearObsCoefficient (originCube 2 (m + hobs)) m t ω) ^ 2)) ≤
        Gbar ω) ∧
      (∫ ω, Gbar ω ∂μ) ≤ Real.sqrt (2 * mainEnvelopeXi ((q3ModelAmplitude M h (m + 1) /
          (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma mainSourceInversePrefix (theta M) t) := by
  intro μ
  classical
  set Q : TriadicCube 2 := originCube 2 (m + hobs) with hQ
  set d : ℕ := 5 + hobs with hd
  set ξ : ℝ := mainEnvelopeXi ((q3ModelAmplitude M h (m + 1) /
    (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma mainSourceInversePrefix (theta M) t with hξ
  have hrow := fun U (hU : U ∈ descendantsAtDepth Q d) =>
    main_envelope_xi_obscell_row M h hM hγ N hpast m hm t ht U
      (observer_cell_scale m hobs U hU)
  let avgΘ : CutoffSample 2 → ℝ := fun ω => descendantsAverage Q d
    (fun U => mixedOldTheta M m U t ω)
  have hΘint : Integrable avgΘ μ := by
    unfold avgΘ descendantsAverage
    exact (integrable_finsetSum _ (fun U hU => (hrow U hU).1)).const_mul _
  have hcardpos : 0 < ((descendantsAtDepth Q d).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (descendantsAtDepth_nonempty Q d)
  have hΘle : (∫ ω, avgΘ ω ∂μ) ≤ ξ := by
    have h1 : (∫ ω, avgΘ ω ∂μ) = ((descendantsAtDepth Q d).card : ℝ)⁻¹ *
        ∑ U ∈ descendantsAtDepth Q d, ∫ ω, mixedOldTheta M m U t ω ∂μ := by
      unfold avgΘ descendantsAverage
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
  let X : CutoffSample 2 → ℝ := fun ω => 2 * avgΘ ω
  have hXint : Integrable X μ := hΘint.const_mul 2
  have hpath := fun ω => observer_parent_paired_le_two_avg_theta M hγ m t ht hobs h40 ω
  have hnn : ∀ ω, 0 ≤ X ω := by
    intro ω
    refine le_trans ?_ (hpath ω)
    unfold descendantsAverage
    exact mul_nonneg (inv_nonneg.mpr hcardpos.le)
      (Finset.sum_nonneg (fun U _ => add_nonneg (sq_nonneg _) (sq_nonneg _)))
  obtain ⟨hVint, hVle⟩ := main_sqrt_expectation_ae μ X hXint
    (Filter.Eventually.of_forall hnn)
  have hXle : (∫ ω, X ω ∂μ) ≤ 2 * ξ := by
    unfold X
    rw [integral_const_mul]
    linarith
  refine ⟨fun ω => Real.sqrt (X ω), hVint, fun ω => Real.sqrt_nonneg _, ?_, ?_, ?_⟩
  · intro ω
    apply Real.sqrt_le_sqrt
    refine le_trans ?_ (hpath ω)
    unfold descendantsAverage
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hcardpos.le)
    exact Finset.sum_le_sum (fun U _ => le_add_of_nonneg_left (sq_nonneg _))
  · intro ω
    exact Real.sqrt_le_sqrt (hpath ω)
  · exact hVle.trans (Real.sqrt_le_sqrt hXle)

end ASDExplicitGamma.Main
