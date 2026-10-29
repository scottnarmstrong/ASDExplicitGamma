module

public import ASDExplicitGamma.Native.ParentBoundaryBandTraceMoments
public import ASDExplicitGamma.Native.ParentRowAffineBill
public import ASDExplicitGamma.Native.ParentRowDerivativePayment
public import ASDExplicitGamma.Native.ParentRowEnergyPayment
public import ASDExplicitGamma.Native.ParentRowFlatPayment

/-! Physical affine payment in the exact parent source fields, retaining the actual cell mean. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Response Variational Inverse Algsuperdiff.Section3
noncomputable section

private theorem affine_payment_scalar (Y v scale D E theta y w a C : ℝ)
    (hE : 0≤E) (hC : 0≤C) (hY : Y≤theta*y) (hv : v≤theta*w)
    (hD : scale*D≤theta*((156/5:ℝ)*a/9)) :
    Y/2*E+2*v*((3683/2500:ℝ)-1)+C*scale*D≤
      theta*(y/2*E+2*w*((3683/2500:ℝ)-1)+C*((156/5:ℝ)*a/9)) := by
  have hy := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hY (by norm_num : (0:ℝ)≤2)) hE
  have hw := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hv (by norm_num : (0:ℝ)≤2))
    (by norm_num : (0:ℝ)≤3683/2500-1)
  have hd := mul_le_mul_of_nonneg_left hD hC
  calc
    _ = (Y/2*E+2*v*((3683/2500:ℝ)-1))+C*(scale*D) := by ring
    _ ≤ (theta*y/2*E+2*(theta*w)*((3683/2500:ℝ)-1))+
        C*(theta*((156/5:ℝ)*a/9)) := add_le_add (add_le_add hy hw) hd
    _ = _ := by ring

/-- All three actual affine contributions fit their stored fields with one theta factor.
The remaining cell mean is the literal expectation to which the proved source mean return applies. -/
theorem parent_row_actual_affine_payment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ) (hstate : nativeInductionState M h n)
    (hpast : ∀ k<n,nativeInductionState M h k) (j : Fin 16)
    (r : ℕ) (hr : r=5) (U : TriadicCube 2)
    (hU : U∈descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (ht : t≤1) :
    (∫ ω,parentBoundaryBandAffineBill M h n (j.val+1) r t ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
    theta M*((parentRowFields j).getD 16 0/2*
      (∫ ω,traceDefect (cubeSet U)
        (attenuatedCoefficient M n (n+((j.val+1:ℕ):ℤ)) (fun _ => Real.sqrt t) ω)
        (Annealed.sigmaBar M n) ∂(Cutoff.cutoffSampleLaw M).toMeasure)+
      2*(parentRowFields j).getD 0 0*((3683/2500:ℝ)-1)+
      (4+2*Real.sqrt 2)*((156/5:ℝ)*(parentRowFields j).getD 1 0/9)) := by
  let E := ∫ ω,traceDefect (cubeSet U)
    (attenuatedCoefficient M n (n+((j.val+1:ℕ):ℤ)) (fun _ => Real.sqrt t) ω)
    (Annealed.sigmaBar M n) ∂(Cutoff.cutoffSampleLaw M).toMeasure
  have hE : 0≤E := integral_nonneg (fun ω =>
    parent_boundary_band_trace_nonneg M n (j.val+1) t U ω)
  have ha := (parent_row_affine_bill M h hM hg n (j.val+1) (Nat.succ_pos _)
    r hr.le U hU t ht hpast).2
  subst r
  exact ha.trans (affine_payment_scalar _ _ _ _ E _ _ _ _ _ hE
    (by positivity) (parent_row_actual_dirichlet_energy M h hg n hstate j)
    (parent_row_actual_variance M h hg n hstate j)
    (parent_row_actual_derivative_payment M h hg n hstate j))

end
end ASDExplicitGamma.Native
