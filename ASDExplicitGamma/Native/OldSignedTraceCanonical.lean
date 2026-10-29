module

public import ASDExplicitGamma.Native.OldSignedCanonicalLoadTrace
public import ASDExplicitGamma.Native.OldSignedFiniteHessianSum
public import ASDExplicitGamma.Native.OldSignedActualHessianTrial
public import ASDExplicitGamma.Variational.LemmaVTrace

/-! The actual normalized trace and its half Hessian are the canonical
four-load responses used by the physical OLD signed trial. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Variational
open ASDExplicitGamma.Gaussian
noncomputable section

/-- The canonical physical response on one of the four top/bottom loads. -/
def oldSignedCanonicalLoadEnergy (m : ℤ) (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (c : BlockCoord 2) : ResponseCoefficient (openCubeSet (originCube 2 m)) → ℝ :=
  responseFrameEnergyObservable (measurableSet_openCubeSet (originCube 2 m))
    (volume_openCubeSet_originCube_toReal_pos (d := 2) m) nu sigma hnu hsigma (blockBasis c)

/-- The literal actual trace defect is the canonical four-load response
sum minus four, with precisely the same physical molecular parameter and frame. -/
theorem old_signed_trace_eq_canonical_sum (m : ℤ) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet (originCube 2 m))) :
    lemmaVTrace m nu sigma k=(∑ c : BlockCoord 2,oldSignedCanonicalLoadEnergy m nu sigma hnu hsigma c k)-4 := by
  rw [lemmaVTrace_eq_load_sum m nu sigma hnu hsigma k,Fintype.sum_prod_type]
  have hp (i : Fin 2) : (∑ b : Bool,lemmaVLoadEnergy m nu sigma hnu hsigma (i,b) k)=
      oldSignedCanonicalLoadEnergy m nu sigma hnu hsigma (Sum.inl i) k+
      oldSignedCanonicalLoadEnergy m nu sigma hnu hsigma (Sum.inr i) k := by
    simpa [Fintype.sum_bool,lemmaVLoadEnergy,lemmaVLoadSign,oldSignedCanonicalLoadEnergy,blockBasis,basisVec,add_comm] using
      old_signed_frame_energy_canonical_pair (measurableSet_openCubeSet (originCube 2 m))
        (volume_openCubeSet_originCube_toReal_pos (d := 2) m) nu sigma hnu hsigma k i
  simp_rw [hp]
  rw [Finset.sum_add_distrib,Fintype.sum_sum_type]

/-- The half directional Hessian of the literal trace is exactly the
sum of the four canonical half Hessians, before using any trial estimate. -/
theorem old_signed_trace_half_hessian (m : ℤ) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma)
    (k H : ResponseCoefficient (openCubeSet (originCube 2 m))) :
    (1/2:ℝ)*fderiv ℝ (fun z => fderiv ℝ (lemmaVTrace m nu sigma) z H) k H=
      ∑ c : BlockCoord 2,(1/2:ℝ)*fderiv ℝ
        (fun z => fderiv ℝ (oldSignedCanonicalLoadEnergy m nu sigma hnu hsigma c) z H) k H := by
  have he : lemmaVTrace m nu sigma=(fun z =>
      (∑ c : BlockCoord 2,oldSignedCanonicalLoadEnergy m nu sigma hnu hsigma c z)-4) :=
    funext (old_signed_trace_eq_canonical_sum m nu sigma hnu hsigma)
  have hd (c : BlockCoord 2) : ContDiff ℝ 2 (oldSignedCanonicalLoadEnergy m nu sigma hnu hsigma c) :=
    responseFrameEnergyObservable_contDiff (measurableSet_openCubeSet (originCube 2 m))
      (volume_openCubeSet_originCube_toReal_pos (d := 2) m) nu sigma hnu hsigma _
  rw [he,old_signed_second_fderiv_sum_sub_const _ hd]
  rw [Finset.mul_sum]

/-- The physical OLD four-load sum is the actual trace's half Hessian
in direction sigma psi, with no covariance or basis identity assumed. -/
theorem old_signed_physical_trace_half_hessian (m : ℤ) (nu sigma : ℝ)
    (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet (originCube 2 m))) (b : ℝ) (L : {l : ℝ // 0<l})
    (n : whiteBasisIndex) :
    let H := oldSignedPhysicalCoefficient (originCube 2 m) sigma b L n
    (1/2:ℝ)*fderiv ℝ (fun z => fderiv ℝ (lemmaVTrace m nu sigma) z H) k H=
      ∑ c : BlockCoord 2,oldSignedPhysicalHessian (originCube 2 m) nu sigma hnu hsigma k (blockBasis c) b L n :=
  old_signed_trace_half_hessian m nu sigma hnu hsigma k _

end
end ASDExplicitGamma.Native
