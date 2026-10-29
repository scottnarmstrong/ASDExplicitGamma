module

public import ASDExplicitGamma.Native.ParentHistoryEndpoint
public import ASDExplicitGamma.Native.ParentBoundaryBandMaxTraceMoment
public import ASDExplicitGamma.Native.OldSignedMatrixHistoryMoments
public import ASDExplicitGamma.Native.OldSignedQ1MatrixMoments

/-! Sharp physical history moments for the simultaneous parent band. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Cold Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- The actual real history inherits the physical endpoint without losing theta. -/
theorem parent_row_real_history_endpoint
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (n : ℤ) (height r : ℕ) (hr : r ≤ 5) (hheight : 1 ≤ height)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) r)
    (hpast : ∀ k<n,nativeInductionState M h k) (hstate : nativeInductionState M h n)
    (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) :
    let H := fun ω => oldSignedMaxTraceHistory U (parentBoundaryBandFrameField M n height t ω)
    MemLp H 2 (Cutoff.cutoffSampleLaw M).toMeasure ∧
    lpNorm H 2 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      theta M*parentHistorySourceEnvelope height r t := by
  intro H
  have hn := parent_boundary_band_max_trace_history_nonneg M n height r U hU t
  have hb := parent_history_physical_endpoint_L2 M h hM hg U n r hr
    (by simpa only [originCube] using scale_eq_sub_of_mem_descendantsAtDepth hU)
    hstate height hheight hpast t ht.1 ht.2
  have he : eLpNorm H 2 (Cutoff.cutoffSampleLaw M).toMeasure =
      eLpNorm (parentBoundaryBandMaxTraceHistory M n height U t) 2
        (Cutoff.cutoffSampleLaw M).toMeasure := by
    calc
      _ = eLpNorm (ENNReal.ofReal ∘ H) 2 (Cutoff.cutoffSampleLaw M).toMeasure :=
        (eLpNorm_ofReal H (Filter.Eventually.of_forall hn)).symm
      _ = _ := eLpNorm_congr_ae (Filter.Eventually.of_forall (fun ω =>
        (parent_boundary_band_max_trace_history M n height r U hU t ω).symm))
  have hc : eLpNorm H 2 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (theta M*parentHistorySourceEnvelope height r t) := he ▸ hb
  refine ⟨hc.trans_lt ENNReal.ofReal_lt_top, ?_⟩
  change (eLpNorm H 2 (Cutoff.cutoffSampleLaw M).toMeasure).toReal ≤ _
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hc).trans_eq
    (ENNReal.toReal_ofReal (mul_nonneg (cold_theta_pos M).le (sq_nonneg _)))

/-- The actual parent cell history supplies both multiplier moments used by the
AN error, retaining theta in the corrector product. No moment cap is assumed. -/
theorem parent_row_matrix_corrector_moments
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ)
    (hpast : ∀ l<n,nativeInductionState M h l) (hstate : nativeInductionState M h n)
    (height r : ℕ) (hr : r ≤ 5) (hheight : 1 ≤ height) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (ht : 0≤t ∧ t≤1) :
    let H := fun ω => oldSignedMaxTraceHistory U (parentBoundaryBandFrameField M n height t ω)
    let A := fun ω => 1+2*H ω+Real.sqrt (2*H ω)
    let C := parentHistorySourceEnvelope height r t
    let B := 1+2*C+Real.sqrt (2*C)
    MemLp A 2 (Cutoff.cutoffSampleLaw M).toMeasure ∧
    lpNorm A 2 (Cutoff.cutoffSampleLaw M).toMeasure ≤ B ∧
    Integrable (fun ω => (1+inverseHistoryDiscount)*A ω*H ω)
      (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,(1+inverseHistoryDiscount)*A ω*H ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      theta M*((1+inverseHistoryDiscount)*B*C) := by
  intro H A C B
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  have hc := parent_row_real_history_endpoint M h hM hg n height r hr hheight U hU hpast hstate t ht
  have hH0 : ∀ ω,0≤H ω := parent_boundary_band_max_trace_history_nonneg M n height r U hU t
  have hC : 0≤C := sq_nonneg _
  have hθ := (cold_theta_pos M).le
  have hθC : 0≤theta M*C := mul_nonneg hθ hC
  have hsmall : theta M*C ≤ C := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (cold_theta_le_one M hg) hC
  have hm := old_signed_matrix_majorant_L2 μ H (theta M*C) hc.1 hH0 hθC hc.2
  have hp := old_signed_matrix_history_product μ H (theta M*C) hc.1 hH0 hθC hc.2
  have hmb : 1+2*(theta M*C)+Real.sqrt (2*(theta M*C)) ≤ B :=
    old_signed_matrix_majorant_mono hsmall
  have hD : 0≤1+inverseHistoryDiscount := add_nonneg (by norm_num) inverse_history_discount_range.1.le
  have hi : Integrable (fun ω => (1+inverseHistoryDiscount)*A ω*H ω) μ := by
    have hh := hp.1.const_mul (1+inverseHistoryDiscount)
    simpa only [mul_assoc] using hh
  refine ⟨hm.1,hm.2.trans hmb,hi,?_⟩
  change (∫ ω,(1+inverseHistoryDiscount)*A ω*H ω ∂μ) ≤ _
  simp_rw [mul_assoc (1+inverseHistoryDiscount)]
  rw [integral_const_mul]
  have hh := mul_le_mul_of_nonneg_left (hp.2.trans
    (mul_le_mul_of_nonneg_right hmb hθC)) hD
  exact hh.trans_eq (by ring)

end
end ASDExplicitGamma.Native
