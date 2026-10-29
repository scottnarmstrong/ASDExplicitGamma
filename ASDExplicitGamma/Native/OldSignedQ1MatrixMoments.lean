module

public import ASDExplicitGamma.Native.OldSignedQ1HistoryEnvelope
public import ASDExplicitGamma.Native.OldSignedMatrixHistoryMoments

/-! Actual matrix and corrector majorant moments for the OLD q1 panel. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Scalar Inverse Cold Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- Monotonicity of the literal matrix-history majorant. -/
theorem old_signed_matrix_majorant_mono {x y : ℝ} (hxy : x≤y) :
    1+2*x+Real.sqrt (2*x) ≤ 1+2*y+Real.sqrt (2*y) :=
  add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hxy (by norm_num : (0:ℝ)≤2)))
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hxy (by norm_num)))

/-- The actual q1 cell history supplies both multiplier moments used by the
AN error, retaining theta in the corrector product. No moment cap is assumed. -/
theorem old_signed_q1_matrix_corrector_moments
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ)
    (hpast : ∀ l ≤ n,nativeInductionState M h l)
    (r : ℕ) (hr : r=5) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (ht : 0≤t ∧ t≤1) :
    let H := fun ω => oldSignedMaxTraceHistory U (oldSignedPartialFrameField M n 1 t ω)
    let A := fun ω => 1+2*H ω+Real.sqrt (2*H ω)
    let C := oldSignedQ1PanelHistory t
    let B := 1+2*C+Real.sqrt (2*C)
    MemLp A 2 (Cutoff.cutoffSampleLaw M).toMeasure ∧
    lpNorm A 2 (Cutoff.cutoffSampleLaw M).toMeasure ≤ B ∧
    Integrable (fun ω => (1+inverseHistoryDiscount)*A ω*H ω)
      (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,(1+inverseHistoryDiscount)*A ω*H ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      theta M*((1+inverseHistoryDiscount)*B*C) := by
  intro H A C B
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  have hc := old_signed_cell_q1_panel_history M h hM hg n hpast r hr U hU t ht
  have hH0 : ∀ ω,0≤H ω := old_signed_actual_max_trace_history_nonneg M n r U hU t
  have hC : 0≤C := sq_nonneg _
  have hθ := (cold_theta_pos M).le
  have hθC : 0≤theta M*C := mul_nonneg hθ hC
  have hsmall : theta M*C ≤ C := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (cold_theta_le_one M hg) hC
  have hm := old_signed_matrix_majorant_L2 μ H (theta M*C) hc.2.1 hH0 hθC hc.2.2
  have hp := old_signed_matrix_history_product μ H (theta M*C) hc.2.1 hH0 hθC hc.2.2
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
