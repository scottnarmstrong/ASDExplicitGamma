module

public import ASDExplicitGamma.Native.GenericSourceInverseTrace
public import ASDExplicitGamma.Inverse.BankOnePassHeat
public import ASDExplicitGamma.Native.VanishingBracket

/-! The source finite-pass inverse-trace bound for the actual coefficient
observable. Coarse trace duality follows by choosing its positive optimal
comparison frame in the all-frame nonnegative defect inequality. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open ASDExplicitGamma.Response
noncomputable section

/-- The compact inverse observable is exactly the physical framed block trace. -/
theorem native_source_model_inverse_trace_eq_frame_trace
    (n : ℤ) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (x : C(closure (cubeSet (originCube 2 n)),ℝ)) :
    bankInverseTraceObservable n ν σ hν hσ x =
      Matrix.trace (frameMatrix σ (coarseBlockMatrix (cubeSet (originCube 2 n))
        (responsePlanarCoefficientField ν
          (ContinuousMap.linearIsometryBoundedOfCompact (closure (cubeSet (originCube 2 n))) ℝ ℝ x)))).lowerRight := by
  rw [bank_inverse_trace_observable_eq]
  simp only [bankInverseTrace,frameMatrix,Matrix.trace,Matrix.diag_apply,Matrix.smul_apply,smul_eq_mul]

/-- The actual compact inverse-trace observable is nonnegative. -/
theorem native_source_model_inverse_trace_nonneg
    (n : ℤ) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (x : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    0 ≤ bankInverseTraceObservable n ν σ hν hσ x := by
  let Q := originCube 2 n
  let k : ResponseCoefficient (cubeSet Q) :=
    ContinuousMap.linearIsometryBoundedOfCompact (closure (cubeSet Q)) ℝ ℝ x
  have hEll := responsePlanarCoefficientField_isElliptic (measurableSet_cubeSet Q) ν hν k
  have hpos := coarseBlockMatrix_posDef hν hEll
  rw [bank_inverse_trace_observable_eq]
  apply Finset.sum_nonneg
  intro i _
  have hh := hpos.diag_pos (i := Sum.inr i)
  apply mul_nonneg hσ.le
  exact hh.le

/-- The actual inverse trace has the scalar bound in every positive
fixed frame. The molecular coefficient remains the same throughout. -/
theorem native_source_model_inverse_trace_le
    (n : ℤ) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (x : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    bankInverseTraceObservable n ν σ hν hσ x ≤
      2+modelTraceObservable n ν σ x+Real.sqrt (2*modelTraceObservable n ν σ x) := by
  let Q := originCube 2 n
  let k : ResponseCoefficient (cubeSet Q) :=
    ContinuousMap.linearIsometryBoundedOfCompact (closure (cubeSet Q)) ℝ ℝ x
  let a := responsePlanarCoefficientField ν k
  let A := coarseBlockMatrix (cubeSet Q) a
  let u := Matrix.trace A.upperLeft
  let v := Matrix.trace A.lowerRight
  have hEll := responsePlanarCoefficientField_isElliptic (measurableSet_cubeSet Q) ν hν k
  have hpos := coarseBlockMatrix_posDef hν hEll
  have hv0 : 0 < A.lowerRight 0 0 := by
    simpa only [A,toFullBlockMat] using hpos.diag_pos (i := Sum.inr (0:Fin 2))
  have hv1 : 0 < A.lowerRight 1 1 := by
    simpa only [A,toFullBlockMat] using hpos.diag_pos (i := Sum.inr (1:Fin 2))
  have hv : 0 < v := by
    simpa only [v,Matrix.trace,Fin.sum_univ_two,Matrix.diag_apply] using add_pos hv0 hv1
  have ht := traceDefect_nonneg_of_ellipticFieldOn_triCube hν hEll (div_pos (by norm_num : (0:ℝ)<2) hv)
  have he : traceDefect (cubeSet Q) a (2/v) = u*v/2-2 := by
    change (2/v)⁻¹*u+(2/v)*v-4=u*v/2-2
    field_simp [hv.ne']
    ring
  rw [he] at ht
  have hprod : (4:ℝ) ≤ (σ⁻¹*u)*(σ*v) := by
    have heq : (σ⁻¹*u)*(σ*v)=u*v := by field_simp [hσ.ne']
    rw [heq]
    linarith only [ht]
  have htrace : modelTraceObservable n ν σ x = σ⁻¹*u+σ*v-4 := rfl
  have ht0 := modelTraceObservable_nonneg n ν σ hν hσ x
  rw [htrace] at ht0
  have hh := native_source_inverse_trace_scalar (σ⁻¹*u) (σ*v) hprod ht0
  have hi : bankInverseTraceObservable n ν σ hν hσ x = σ*v := by
    rw [bank_inverse_trace_observable_eq]
    dsimp [bankInverseTrace,v,A,a,k,Q]
    simp only [Matrix.trace,Finset.mul_sum,Matrix.diag_apply]
  rw [hi,htrace]
  exact hh

end
end ASDExplicitGamma.Native
