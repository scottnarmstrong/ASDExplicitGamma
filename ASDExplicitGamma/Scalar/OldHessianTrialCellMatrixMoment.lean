module

public import ASDExplicitGamma.Scalar.OldHessianTrialCellMaxMoment
public import ASDExplicitGamma.Native.OldSignedQ1MatrixMoments
public import ASDExplicitGamma.Scalar.OldHessianTrialGroupedRealBank
public import ASDExplicitGamma.Native.OldSignedL2ProductExpectation
public import ASDExplicitGamma.Numerics.Scalar.Lower

/-! Actual fine-cell matrix moments at the sharp scalar Hsrc endpoint. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Cold Algsuperdiff.Section3
open Numerics.Mirror Numerics.Scalar
open scoped ENNReal
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- The actual physical matrix-history majorant on an individual source cell. -/
def oldHessianCellMatrixMajorant (M : ABKModel 2) (m : ℤ) (U : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  let H := oldHessianCellMaxTraceHistory M m U ω
  1+2*H+Real.sqrt (2*H)

/-- The fine-cell matrix and corrector moments consume the same actual
max history and retain its theta scaling, with the frozen Mstar constant. -/
theorem old_hessian_cell_matrix_moments
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N)
    (U : TriadicCube 2) (hU : U∈descendantsAtDepth (originCube 2 (m+129)) 134) :
    MemLp (oldHessianCellMatrixMajorant M m U) 2 (Cutoff.cutoffSampleLaw M).toMeasure ∧
      lpNorm (oldHessianCellMatrixMajorant M m U) 2 (Cutoff.cutoffSampleLaw M).toMeasure≤evalReal scalarRealEnv lowerMExpr ∧
    Integrable (fun ω => (1+inverseHistoryDiscount)*oldHessianCellMatrixMajorant M m U ω*
      oldHessianCellMaxTraceHistory M m U ω) (Cutoff.cutoffSampleLaw M).toMeasure ∧
      (∫ ω,(1+inverseHistoryDiscount)*oldHessianCellMatrixMajorant M m U ω*
        oldHessianCellMaxTraceHistory M m U ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
          theta M*((44/25:ℝ)*evalReal scalarRealEnv lowerMExpr*(5423/2500:ℝ)) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let H := oldHessianCellMaxTraceHistory M m U
  let C := theta M*(5423/2500:ℝ)
  have hc := old_hessian_cell_max_trace_L2 M h hM hg N hpast m hm U hU
  have hH0 := old_hessian_cell_max_trace_nonneg M m U hU
  have hC : 0≤C := mul_nonneg (cold_theta_pos M).le (by norm_num)
  have hsmall : C≤(5423/2500:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right (cold_theta_le_one M hg) (by norm_num : (0:ℝ)≤5423/2500)
    rw [one_mul] at hh
    exact hh
  have hm := old_signed_matrix_majorant_L2 μ H C hc.1 hH0 hC hc.2
  have hp := old_signed_matrix_history_product μ H C hc.1 hH0 hC hc.2
  have hmajor : 1+2*C+Real.sqrt (2*C)≤evalReal scalarRealEnv lowerMExpr :=
    (old_signed_matrix_majorant_mono hsmall).trans_eq (by norm_num [evalReal,lowerMExpr,sc])
  have hD0 : 0≤1+inverseHistoryDiscount := add_nonneg (by norm_num) inverse_history_discount_range.1.le
  have hD : 1+inverseHistoryDiscount≤(44/25:ℝ) := by
    linarith only [old_signed_initial_history_tail_gates.1]
  have hi : Integrable (fun ω => (1+inverseHistoryDiscount)*oldHessianCellMatrixMajorant M m U ω*H ω) μ := by
    simpa only [oldHessianCellMatrixMajorant, H, mul_assoc] using hp.1.const_mul (1+inverseHistoryDiscount)
  refine ⟨hm.1,hm.2.trans hmajor,hi,?_⟩
  simp_rw [mul_assoc (1+inverseHistoryDiscount)]
  rw [integral_const_mul]
  have hprod := mul_le_mul_of_nonneg_right hmajor hC
  have hnon : 0≤evalReal scalarRealEnv lowerMExpr*C := by
    have hm0 : 0≤evalReal scalarRealEnv lowerMExpr := by
      norm_num [evalReal,lowerMExpr,sc]
      positivity
    exact mul_nonneg hm0 hC
  have hh := mul_le_mul hD (hp.2.trans hprod) (integral_nonneg
    (fun ω => mul_nonneg (add_nonneg (add_nonneg (by norm_num) (mul_nonneg (by norm_num) (hH0 ω)))
      (Real.sqrt_nonneg _)) (hH0 ω))) (by norm_num : (0:ℝ)≤44/25)
  exact hh.trans_eq (by dsimp only [C]; ring)

/-- The same original grouped inverse bank remains correlated with each
cell's matrix majorant and pays exactly beta Mstar. -/
theorem old_hessian_cell_bank_matrix_moment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N)
    (U : TriadicCube 2) (hU : U∈descendantsAtDepth (originCube 2 (m+129)) 134) :
    Integrable (fun ω => oldHessianGroupedBank M m ω*oldHessianCellMatrixMajorant M m U ω)
      (Cutoff.cutoffSampleLaw M).toMeasure ∧
      (∫ ω,oldHessianGroupedBank M m ω*oldHessianCellMatrixMajorant M m U ω
        ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤(14103/10000:ℝ)*evalReal scalarRealEnv lowerMExpr := by
  have hbank := old_hessian_actual_grouped_real_bank M h hM hg N hpast m hm
  have hb2 : eLpNorm (oldHessianGroupedBank M m) 2 (Cutoff.cutoffSampleLaw M).toMeasure≤
      ENNReal.ofReal (14103/10000:ℝ) :=
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (2:ℝ≥0∞)≤128)).trans hbank.2.2.1
  have hb : MemLp (oldHessianGroupedBank M m) 2 (Cutoff.cutoffSampleLaw M).toMeasure :=
    hb2.trans_lt ENNReal.ofReal_lt_top
  have hbn : lpNorm (oldHessianGroupedBank M m) 2 (Cutoff.cutoffSampleLaw M).toMeasure≤(14103/10000:ℝ) := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb2
    rw [ENNReal.toReal_ofReal (by norm_num : (0:ℝ)≤14103/10000)] at hh
    exact hh
  have hm := old_hessian_cell_matrix_moments M h hM hg N hpast m hm U hU
  have hmatrix0 (ω) : 0≤oldHessianCellMatrixMajorant M m U ω :=
    add_nonneg (add_nonneg (by norm_num) (mul_nonneg (by norm_num)
      (old_hessian_cell_max_trace_nonneg M m U hU ω))) (Real.sqrt_nonneg _)
  exact old_signed_L2_product_expectation (Cutoff.cutoffSampleLaw M).toMeasure _ _ _ _ hb hm.1
    (fun _ => ENNReal.toReal_nonneg) hmatrix0 (by norm_num) hbn hm.2.1

end
end ASDExplicitGamma.Scalar
