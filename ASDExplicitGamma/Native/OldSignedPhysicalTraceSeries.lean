module

public import ASDExplicitGamma.Native.OldSignedTraceCanonical
public import ASDExplicitGamma.Native.OldSignedPhysicalDirections

/-! Genuine convergence of the physical OLD Hessian family and exact
recovery of the actual q3 covariance trace from its complete white-mode sum. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Variational
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse
noncomputable section

/-- Each actual physical affine-load Hessian family is genuinely summable. -/
theorem old_signed_physical_hessian_summable (m : ℤ) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet (originCube 2 m))) (P : BlockVec 2)
    (b : ℝ) (L : {l : ℝ // 0<l}) :
    Summable (oldSignedPhysicalHessian (originCube 2 m) nu sigma hnu hsigma k P b L) := by
  let E := responseFrameEnergyObservable (measurableSet_openCubeSet (originCube 2 m))
    (volume_openCubeSet_originCube_toReal_pos (d := 2) m) nu sigma hnu hsigma P
  have hd : ContDiff ℝ 2 E := responseFrameEnergyObservable_contDiff _ _ nu sigma hnu hsigma P
  have hs := (pureFlux_secondDirectionalDerivative_summable E hd
    (pureFluxMainCubeQ3ResponseCoefficient m (sigma*b) L)
    (main_q3_responseCoefficient_summable m (sigma*b) L) k).mul_left (1/2:ℝ)
  have hh := hs.comp_injective
    (@Encodable.encode_injective whiteBasisIndex (Encodable.ofCountable whiteBasisIndex))
  change Summable (fun n : whiteBasisIndex => (1/2:ℝ)*secondDirectionalDerivative E k
    (pureFluxMainCubeQ3ResponseCoefficient m (sigma*b) L
      (@Encodable.encode whiteBasisIndex (Encodable.ofCountable whiteBasisIndex) n))) at hh
  simp_rw [old_signed_physical_direction_eq] at hh
  exact hh

/-- All four canonical physical Hessians have a genuine complete sum. -/
theorem old_signed_physical_trace_summable (m : ℤ) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet (originCube 2 m))) (b : ℝ) (L : {l : ℝ // 0<l}) :
    Summable (fun n : whiteBasisIndex => ∑ c : BlockCoord 2,
      oldSignedPhysicalHessian (originCube 2 m) nu sigma hnu hsigma k (blockBasis c) b L n) :=
  summable_sum (fun c _ => old_signed_physical_hessian_summable m nu sigma hnu hsigma k (blockBasis c) b L)

/-- The actual physical OLD canonical sum is exactly half of the q3
covariance trace at amplitude sigma b, with no covariance hypothesis. -/
theorem old_signed_physical_trace_eq_covariance (m : ℤ) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet (originCube 2 m))) (b : ℝ) (L : {l : ℝ // 0<l}) :
    (1/2:ℝ)*modelCovarianceTrace (lemmaVTrace m nu sigma)
      (pureFluxMainCubeQ3ResponseCoefficient m (sigma*b) L) k=
      ∑' n : whiteBasisIndex,∑ c : BlockCoord 2,
        oldSignedPhysicalHessian (originCube 2 m) nu sigma hnu hsigma k (blockBasis c) b L n := by
  let f := fun H : ResponseCoefficient (openCubeSet (originCube 2 m)) =>
    (1/2:ℝ)*secondDirectionalDerivative (lemmaVTrace m nu sigma) k H
  have hf : f 0=0 := by simp [f,secondDirectionalDerivative]
  calc
    _ = ∑' j,f (pureFluxMainCubeQ3ResponseCoefficient m (sigma*b) L j) := tsum_mul_left.symm
    _ = ∑' n : whiteBasisIndex,f (pureFluxMainCubeQ3ResponseCoefficient m (sigma*b) L
        (@Encodable.encode whiteBasisIndex (Encodable.ofCountable whiteBasisIndex) n)) :=
      main_q3_directions_tsum_apply m (sigma*b) L f hf
    _ = _ := by
      apply tsum_congr
      intro n
      rw [old_signed_physical_direction_eq]
      exact old_signed_physical_trace_half_hessian m nu sigma hnu hsigma k b L n

end
end ASDExplicitGamma.Native
