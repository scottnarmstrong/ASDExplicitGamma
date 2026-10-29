module

public import ASDExplicitGamma.Main.ThetaGeneratorObserverParentGapExpectation

/-! Generator assembly: the domain gate `ξ - b_o f ≥ 0` at an observer root, from
`E V² ≥ 0` (copy of the first half of `observer_parent_gap_row_Th`). -/

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

/-- Domain condition at the observer root: `ξ(t) - b_o f(t) ≥ 0` (E V² ≥ 0). -/
theorem hot_observer_xi_domain_Th
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ l < N, nativeInductionState M h l)
    (m : ℤ) (hm : m < N) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hobs : ℕ) (h40 : hobs ≤ 40) :
    0 ≤ mainEnvelopeXi ((q3ModelAmplitude M h (m + 1) /
        (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma (theta M * mainSourceInversePrefix) (theta M) t -
      mainBetaOld * modelTraceHeatAverage (m + hobs) M m t := by
  classical
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  set Q : TriadicCube 2 := originCube 2 (m + hobs) with hQ
  set d : ℕ := 5 + hobs with hd
  set ξ : ℝ := mainEnvelopeXi ((q3ModelAmplitude M h (m + 1) /
    (Annealed.sigmaBar M m : ℝ)) ^ 2) M.gamma (theta M * mainSourceInversePrefix) (theta M) t with hξ
  set f : ℝ := modelTraceHeatAverage (m + hobs) M m t with hf
  set C : ℝ := 3683 / 2500 with hC
  have hrow := fun U (hU : U ∈ descendantsAtDepth Q d) =>
    main_envelope_xi_obscell_row_Th M h hM hγ N hpast m hm t ht U
      (observer_cell_scale_Th m hobs U hU)
  have hanchor := observer_anchor_integrable_Th M h hM hγ N hpast m hm t ht hobs
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
  let A : CutoffSample 2 → ℝ := fun ω => rawCubeFourLoadTrace M m Q t ω
  have hAint : Integrable A μ := hanchor.1
  have hAmean : (∫ ω, A ω ∂μ) = f := hanchor.2
  let X : CutoffSample 2 → ℝ := fun ω => avgΘ ω - C * A ω
  have hXint : Integrable X μ := hΘint.sub (hAint.const_mul C)
  have hXle : (∫ ω, X ω ∂μ) ≤ ξ - C * f := by
    have : (∫ ω, X ω ∂μ) = (∫ ω, avgΘ ω ∂μ) - C * ∫ ω, A ω ∂μ := by
      unfold X
      rw [integral_sub hΘint (hAint.const_mul C), integral_const_mul]
    rw [this, hAmean]
    linarith
  have hpath : ∀ ω, descendantsAverage Q d (fun U =>
      oldSignedPrimalErrorSize Q U M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos
        (Annealed.sigmaBar_characterization M m).1
        (mainELinearObsCoefficient Q m t ω) ^ 2) ≤ X ω := by
    intro ω
    have hp := observer_parent_primal_le_avg_theta M hγ m t ht hobs h40 ω
    have hAeq : traceDefect (openCubeSet Q)
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
          (mainELinearObsCoefficient Q m t ω)) 1 = A ω := by
      have hQ0 : Q ∈ descendantsAtDepth Q 0 := by simp
      exact obs_partial_trace_cell_eq_raw M m t ht ω Q _
        (fun x hx => old_signed_obs_frame_eq_scaled_partial M Q m t ω x hx) Q 0 hQ0
    unfold X avgΘ
    rw [← hAeq]
    exact hp
  have hnn : ∀ ω, 0 ≤ X ω := by
    intro ω
    refine le_trans ?_ (hpath ω)
    unfold descendantsAverage
    exact mul_nonneg (inv_nonneg.mpr hcardpos.le)
      (Finset.sum_nonneg (fun U _ => sq_nonneg _))
  have h0 : 0 ≤ ∫ ω, X ω ∂μ := integral_nonneg hnn
  have hC' : mainBetaOld = C := by norm_num [mainBetaOld, hC]
  rw [hC']
  linarith

end ASDExplicitGamma.Main
