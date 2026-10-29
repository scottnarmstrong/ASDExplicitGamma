module

public import ASDExplicitGamma.Native.OldSignedTrialFields
public import ASDExplicitGamma.Native.OldSignedShearFieldTransport

/-! The localized-source gauge cancels against the global flat gradient.
The cancellation is global; no cellwise source-patch identity is asserted. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Variational
noncomputable section

/-- A genuine zero-normal solenoidal gauge leaves every parent gradient
pairing unchanged, with all integrability supplied explicitly. -/
theorem old_signed_gradient_gauge_pairing (Q : TriadicCube 2)
    (u : H1Function (openCubeSet Q)) (F G : Vec 2 → Vec 2)
    (hF : MemVectorL2 (openCubeSet Q) F) (hG : MemVectorL2 (openCubeSet Q) G)
    (hsol : IsSolenoidalZeroNormalTraceOn (openCubeSet Q) (fun x => F x-G x)) :
    volumeAverage (openCubeSet Q) (fun x => vecDot (u.grad x) (F x))=
      volumeAverage (openCubeSet Q) (fun x => vecDot (u.grad x) (G x)) := by
  have hiF := integrableOn_vecDot_of_memVectorL2 hF u.grad_memVectorL2
  have hiG := integrableOn_vecDot_of_memVectorL2 hG u.grad_memVectorL2
  have hz := hsol u
  have hdot (x : Vec 2) : vecDot (F x-G x) (u.grad x)=
      vecDot (F x) (u.grad x)-vecDot (G x) (u.grad x) := by
    simp [vecDot,sub_mul,Finset.sum_sub_distrib]
  simp_rw [hdot] at hz
  rw [integral_sub hiF hiG] at hz
  have he := sub_eq_zero.mp hz
  unfold volumeAverage
  have hcF : (fun x => vecDot (u.grad x) (F x))=(fun x => vecDot (F x) (u.grad x)) :=
    funext (fun _ => vecDot_comm _ _)
  have hcG : (fun x => vecDot (u.grad x) (G x))=(fun x => vecDot (G x) (u.grad x)) :=
    funext (fun _ => vecDot_comm _ _)
  rw [hcF,hcG,he]

/-- The actual localized OLD-error source has exactly the same global
plus-flat pairing as the physical multiplier. This supplies the flat
covariance cancellation without discarding a local interface flux. -/
theorem old_signed_actual_plus_flat_gauge_pairing (Q : TriadicCube 2) (mesh : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2)
    (b : ℝ) (L : {l : ℝ // 0<l}) (n : whiteBasisIndex) (i : Fin 2) :
    let F := oldSignedFlatPlusBlock Q b L n i
    let H := oldSignedFrameOldErrorSource Q mesh nu sigma hnu hsigma k b L n P
    let C := oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
      ((oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P : Vec 2 → BlockVec 2)-fun _ => P)
    volumeAverage (openCubeSet Q) (fun x => vecDot (F x).2 (H x).2)=
      volumeAverage (openCubeSet Q) (fun x => vecDot (F x).2 (C x).2) := by
  intro F H C
  let a := responseFramePlanarCoefficientField nu sigma k
  let hEll := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
    nu sigma hnu hsigma k
  have hH := old_signed_frame_old_error_source_memL2 Q mesh nu sigma hnu hsigma k b L n P
  have hC : MemBlockL2 (openCubeSet Q) C := old_signed_physical_shear_field_memL2 Q sigma b hsigma L n
    (old_signed_canonical_error_variation Q a hEll P).1
  have hvar := old_signed_old_error_source_gauge_variation Q mesh a hEll b L n P
  obtain ⟨u,hu⟩ := old_signed_flat_plus_potential Q b L n i
  have hh := old_signed_gradient_gauge_pairing Q (-u) (fun x => (H x).2) (fun x => (C x).2)
    (memVectorL2_snd_of_memBlockL2 hH) (memVectorL2_snd_of_memBlockL2 hC) hvar.2.2
  have he : (-u).grad=(fun x => (F x).2) := by
    rw [H1Function.neg_grad,hu]
    rfl
  rw [he] at hh
  exact hh

end
end ASDExplicitGamma.Native
