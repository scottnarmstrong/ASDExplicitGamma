module

public import ASDExplicitGamma.Native.ParentBoundaryTopPairing
public import ASDExplicitGamma.Native.OldSignedTopCovarianceBill
public import ASDExplicitGamma.Main.HotPatchTrial

/-! The top flat covariance of the hot-patched trial equals the old one by the
gauge pairing, hence obeys the same `2 beta_U V_U` bill. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian Main Triadic Variational
noncomputable section

/-- The flat plus pairing against the hot source is its pairing against the
physical shear of the canonical error. -/
theorem hot_plus_flat_gauge_pairing (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2)
    (b : ℝ) (L : {l : ℝ // 0<l}) (n : whiteBasisIndex) (i : Fin 2) :
    let F := oldSignedFlatPlusBlock Q b L n i
    let H := hotPatchSource Q depth depth nu sigma hnu hsigma k b L n P
    let C := oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
      ((oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P : Vec 2 → BlockVec 2)-fun _ => P)
    volumeAverage (openCubeSet Q) (fun x => vecDot (F x).2 (H x).2)=
      volumeAverage (openCubeSet Q) (fun x => vecDot (F x).2 (C x).2) := by
  intro F H C
  let a := responseFramePlanarCoefficientField nu sigma k
  let hEll := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
    nu sigma hnu hsigma k
  have hH := hot_patch_source_memL2 Q depth depth nu sigma hnu hsigma k b L n P
  have hC : MemBlockL2 (openCubeSet Q) C := old_signed_physical_shear_field_memL2 Q sigma b hsigma L n
    (old_signed_canonical_error_variation Q a hEll P).1
  have hvar := hot_patch_source_gauge_variation Q depth depth nu sigma hnu hsigma k b L n P
  obtain ⟨u,hu⟩ := old_signed_flat_plus_potential Q b L n i
  have hh := old_signed_gradient_gauge_pairing Q (-u) (fun x => (H x).2) (fun x => (C x).2)
    (memVectorL2_snd_of_memBlockL2 hH) (memVectorL2_snd_of_memBlockL2 hC) hvar.2.2
  have he : (-u).grad=(fun x => (F x).2) := by
    rw [H1Function.neg_grad,hu]
    rfl
  rw [he] at hh
  exact hh

/-- The hot top-flat covariance is the old one, load by load and mode by mode. -/
theorem hot_top_flat_pairing_eq_old (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0<l}) (n : whiteBasisIndex) (i : Fin 2) :
    volumeAverage (openCubeSet Q) (fun x =>
      vecDot (oldSignedFlatPlusBlock Q b L n i x).2
        (hotPatchSource Q depth depth nu sigma hnu hsigma k b L n (basisVec i,0) x).2) =
    volumeAverage (openCubeSet Q) (fun x =>
      vecDot (oldSignedFlatPlusBlock Q b L n i x).2
        (oldSignedFrameOldErrorSource Q depth nu sigma hnu hsigma k b L n (basisVec i,0) x).2) := by
  rw [hot_plus_flat_gauge_pairing Q depth nu sigma hnu hsigma k (basisVec i,0) b L n i,
    ← old_signed_actual_plus_flat_gauge_pairing Q depth nu sigma hnu hsigma k (basisVec i,0) b L n i]

/-- The hot-patched top covariance obeys the old `2 beta V` bill. -/
theorem hot_top_covariance_bill (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l}) :
    let f := fun n : whiteBasisIndex => 2*∑ i : Fin 2,volumeAverage (openCubeSet Q) (fun x =>
      vecDot (oldSignedFlatPlusBlock Q b L n i x).2
        (hotPatchSource Q depth depth nu sigma hnu hsigma k b L n (basisVec i,0) x).2)
    Summable f ∧ |∑' n,f n|≤2*descendantsAverage Q depth (fun U =>
      oldSignedCovarianceBeta Q U b L true*oldSignedPrimalErrorSize Q U nu sigma hnu hsigma k) := by
  intro f
  have hfe : f = fun n : whiteBasisIndex => 2*∑ i : Fin 2,volumeAverage (openCubeSet Q) (fun x =>
      vecDot (oldSignedFlatPlusBlock Q b L n i x).2
        (oldSignedFrameOldErrorSource Q depth nu sigma hnu hsigma k b L n (basisVec i,0) x).2) := by
    funext n
    simp only [f, hot_top_flat_pairing_eq_old Q depth nu sigma hnu hsigma k b L n]
  rw [hfe]
  exact old_signed_actual_top_covariance_bill Q depth nu sigma hnu hsigma k b L

end
end ASDExplicitGamma.Native
