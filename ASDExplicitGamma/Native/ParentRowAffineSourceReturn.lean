module

public import ASDExplicitGamma.Native.ParentRowAffinePayment
public import ASDExplicitGamma.Native.ParentRowMeanReturn
public import ASDExplicitGamma.Cold.NativeThetaScaling

/-! The complete affine source payment with the actual mean estimate discharged. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Response Variational Inverse Cold Algsuperdiff.Section3
noncomputable section

/-- The stored Dirichlet clock is nonnegative at every configured parent depth. -/
theorem parent_row_y_nonneg (j : Fin 16) : 0≤(parentRowFields j).getD 16 0 := by
  rw [parent_row_y_eq]
  unfold parentRowWeightedClock
  apply Finset.sum_nonneg
  intro i _
  unfold parentRowYWeight nativeSourceShellClock
  norm_num only [gammaZero]
  positivity

/-- The actual affine source bill is controlled by the proved initial mean and source slope.
No cell-mean, moment, generator, or coefficient estimate is an input. -/
theorem parent_row_affine_source_return
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ) (hstate : nativeInductionState M h n)
    (hpast : ∀ k<n,nativeInductionState M h k) (j : Fin 16)
    (r : ℕ) (hr : r=5) (U : TriadicCube 2)
    (hU : U∈descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (ht0 : 0≤t) (ht1 : t≤1) :
    (∫ ω,parentBoundaryBandAffineBill M h n (j.val+1) r t ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
    theta M*((parentRowFields j).getD 16 0/2*
      (nativeSourceGenericMeanProfile gammaZero 1 5+
        t*parentBoundaryMeanSourceSlope gammaZero (j.val+1))+
      2*(parentRowFields j).getD 0 0*((3683/2500:ℝ)-1)+
      (4+2*Real.sqrt 2)*((156/5:ℝ)*(parentRowFields j).getD 1 0/9)) := by
  let E := ∫ ω,traceDefect (cubeSet U)
    (attenuatedCoefficient M n (n+((j.val+1:ℕ):ℤ)) (fun _ => Real.sqrt t) ω)
    (Annealed.sigmaBar M n) ∂(Cutoff.cutoffSampleLaw M).toMeasure
  let A := nativeSourceGenericMeanProfile gammaZero 1 5+
    t*parentBoundaryMeanSourceSlope gammaZero (j.val+1)
  have hmean : E≤theta M*A := parent_row_actual_mean_return M h hM hg n
    (j.val+1) (Nat.succ_pos _) hstate hpast r hr U hU t ht0 ht1
  have hE : 0≤E := integral_nonneg (fun ω =>
    parent_boundary_band_trace_nonneg M n (j.val+1) t U ω)
  have hA : 0≤A := nonneg_of_mul_nonneg_right (hE.trans hmean) (cold_theta_pos M)
  have hmean' : E≤A := hmean.trans
    ((mul_le_mul_of_nonneg_right (cold_theta_le_one M hg) hA).trans_eq (one_mul _))
  have hp := mul_le_mul_of_nonneg_left hmean'
    (div_nonneg (parent_row_y_nonneg j) (by norm_num : (0:ℝ)≤2))
  have ha := parent_row_actual_affine_payment M h hM hg n hstate hpast j r hr U hU t ht1
  exact ha.trans (mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add hp le_rfl) le_rfl) (cold_theta_pos M).le)

end
end ASDExplicitGamma.Native
