module

public import ASDExplicitGamma.Scalar.OldHessianTrialFullAffineSplit
public import ASDExplicitGamma.Scalar.OldHessianTrialCenteredAffinePairing

/-! Complete actual full affine covariance in the original completed OLD law. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Algsuperdiff.Section3
noncomputable section

/-- The actual full positive-source/affine-receiver mode with its exact
trial coefficient. Its fine projection and original minus means are unchanged. -/
def oldHessianFullAffineTerm (M : ABKModel 2) (m : ℤ) (b : ℝ)
    (n : whiteBasisIndex) (ω : Cutoff.CutoffSample 2) : ℝ :=
  (2*(431/500:ℝ))*oldHessianFullAffineSpatialMode (originCube 2 (m+129)) 133 M.nu
    (Annealed.sigmaBar M m) M.nu_pos (Annealed.sigmaBar_characterization M m).1
    (oldHessianOldOpenCoefficient (m+129) m ω) b (q3ModelLength (m+1)) n

/-- Complete actual full affine source identity. The principal, retained
finite-parent covariance and centered residual have precisely the source signs.
No mode convergence, covariance or regularity bound is assumed. -/
theorem old_hessian_actual_full_affine_identity
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ l<N,nativeInductionState M h l) (m : ℤ) (hm : m<N) (b : ℝ) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      let Q := originCube 2 (m+129)
      let k := oldHessianOldOpenCoefficient (m+129) m ω
      HasSum (fun n => oldHessianFullAffineTerm M m b n ω)
        (-(431/500:ℝ)*b^2*oldHessianPrincipalSpatialCross Q 133 M.nu (Annealed.sigmaBar M m)
          M.nu_pos (Annealed.sigmaBar_characterization M m).1 k-
         (2*(431/500:ℝ))*oldHessianCovarianceSpatialCross Q 133 M.nu (Annealed.sigmaBar M m)
          M.nu_pos (Annealed.sigmaBar_characterization M m).1 k b (q3ModelLength (m+1))+
         (2*(431/500:ℝ))*(∑' p,oldHessianCenteredAffineTerm M m b p ω)) := by
  filter_upwards [old_hessian_actual_centered_affine_pairing M h hM hg N hpast m hm b] with ω hω
  let Q := originCube 2 (m+129)
  let k := oldHessianOldOpenCoefficient (m+129) m ω
  let L := q3ModelLength (m+1)
  let C := fun p => oldHessianCenteredAffineTerm M m b p ω
  have hc : Summable (fun n => ∑ i : Fin 2,C (n,i)) := by
    simpa only [tsum_fintype] using hω.1.prod
  have htotal : (∑' n,∑ i : Fin 2,C (n,i))=∑' p,C p := by
    simpa only [tsum_fintype] using hω.1.tsum_prod.symm
  have hcs : HasSum (fun n => (2*(431/500:ℝ))*(∑ i : Fin 2,C (n,i)))
      ((2*(431/500:ℝ))*(∑' p,C p)) := by
    have hh := hc.hasSum.mul_left (2*(431/500:ℝ))
    rw [htotal] at hh
    exact hh
  have hf := old_hessian_frozen_spatial_contraction Q 133 M.nu (Annealed.sigmaBar M m) M.nu_pos
    (Annealed.sigmaBar_characterization M m).1 k b L (431/500)
  have hh := hf.add hcs
  exact hh.congr_fun (fun n => old_hessian_full_affine_mode_split Q 133 M.nu (Annealed.sigmaBar M m)
    M.nu_pos (Annealed.sigmaBar_characterization M m).1 k b L (431/500) n)

end
end ASDExplicitGamma.Scalar
