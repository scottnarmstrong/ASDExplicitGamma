module

public import ASDExplicitGamma.Native.ParentBoundaryTrial
public import ASDExplicitGamma.Native.OldSignedTopFlatPairing

/-! Global parent-source gauge pairing and actual plus-flat covariance
identity, with the same complete physical flat modes. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Gaussian Main Triadic Variational
noncomputable section

/-- Exact actual parent-source flat pairing, before taking norms. -/
theorem parent_boundary_plus_flat_gauge_pairing (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2)
    (b : ℝ) (L : {l : ℝ // 0<l}) (n : whiteBasisIndex) (i : Fin 2) :
    let F := oldSignedFlatPlusBlock Q b L n i
    let H := parentBoundaryOldSource Q nu sigma hnu hsigma k b L n P
    let C := oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
      ((oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P : Vec 2 → BlockVec 2)-fun _ => P)
    volumeAverage (openCubeSet Q) (fun x => vecDot (F x).2 (H x).2)=
      volumeAverage (openCubeSet Q) (fun x => vecDot (F x).2 (C x).2) := by
  intro F H C
  let a := responseFramePlanarCoefficientField nu sigma k
  let hEll := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
    nu sigma hnu hsigma k
  have hH := parent_boundary_old_source_memL2 Q nu sigma hnu hsigma k b L n P
  have hC : MemBlockL2 (openCubeSet Q) C := old_signed_physical_shear_field_memL2 Q sigma b hsigma L n
    (old_signed_canonical_error_variation Q a hEll P).1
  have hvar := parent_boundary_old_source_gauge Q nu sigma hnu hsigma k b L n P
  obtain ⟨u,hu⟩ := old_signed_flat_plus_potential Q b L n i
  have hh := old_signed_gradient_gauge_pairing Q (-u) (fun x => (H x).2) (fun x => (C x).2)
    (memVectorL2_snd_of_memBlockL2 hH) (memVectorL2_snd_of_memBlockL2 hC) hvar.2.2
  have he : (-u).grad=(fun x => (F x).2) := by
    rw [H1Function.neg_grad,hu]
    rfl
  rw [he] at hh
  exact hh


/-- Exact actual parent-source flat pairing, before taking norms. -/
theorem parent_boundary_top_flat_pairing (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0<l}) (n : whiteBasisIndex) (i : Fin 2) :
    let a := responseFramePlanarCoefficientField nu sigma k
    let hEll := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
      nu sigma hnu hsigma k
    volumeAverage (openCubeSet Q) (fun x =>
      vecDot (oldSignedFlatPlusBlock Q b L n i x).2
        (parentBoundaryOldSource Q nu sigma hnu hsigma k b L n (basisVec i,0) x).2)=
    -(∑ j : Fin 2,∫ x,oldSignedTopPrimalError Q a hEll i x j*
      q3Convolution b L h3Zero (whiteBasis n) x*
      matVecMul responsePlanarJ (fun l => mainFlatPlusCoordinate Q b L n (i,l) x) j
        ∂normalizedCubeMeasure Q) := by
  intro a hEll
  rw [parent_boundary_plus_flat_gauge_pairing Q nu sigma hnu hsigma k (basisVec i,0) b L n i]
  have hpoint : (fun x => vecDot (oldSignedFlatPlusBlock Q b L n i x).2
      ((oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n)))
        ((oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (basisVec i,0) : Vec 2 → BlockVec 2)-fun _ => (basisVec i,0)) x).2)=
      fun x => -(∑ j : Fin 2,oldSignedTopPrimalError Q a hEll i x j*
        q3Convolution b L h3Zero (whiteBasis n) x*
        matVecMul responsePlanarJ (fun l => mainFlatPlusCoordinate Q b L n (i,l) x) j) := by
    funext x
    change vecDot (-(fun j => mainFlatPlusCoordinate Q b L n (i,j) x))
      (-(q3Convolution b L h3Zero (whiteBasis n) x • matVecMul responsePlanarJ
        ((oldSignedCanonicalAffineField Q a hEll (basisVec i,0) x).1-basisVec i)))= _
    exact old_signed_rotated_flat_pairing _ _ _
  have hi (j : Fin 2) : Integrable (fun x => oldSignedTopPrimalError Q a hEll i x j*
      q3Convolution b L h3Zero (whiteBasis n) x*
      matVecMul responsePlanarJ (fun l => mainFlatPlusCoordinate Q b L n (i,l) x) j)
        (normalizedCubeMeasure Q) := by
    let u : H1Function (openCubeSet Q) := ∑ l : Fin 2,responsePlanarJ j l • mainFlatPlusCoordinate Q b L n (i,l)
    have hu : u.toFun=(fun x => matVecMul responsePlanarJ (fun l => mainFlatPlusCoordinate Q b L n (i,l) x) j) := by
      simp only [u,Fin.sum_univ_two,H1Function.add_toFun,H1Function.smul_toFun]
      funext x
      simp only [matVecMul,Fin.sum_univ_two]
    have hw : MemLp (fun x => matVecMul responsePlanarJ (fun l => mainFlatPlusCoordinate Q b L n (i,l) x) j)
        2 (normalizedCubeMeasure Q) := by rw [←hu]; exact u.memL2_normalizedCubeMeasure
    exact old_signed_physical_mode_pairing_integrable Q b L n _ _
      (old_signed_top_primal_error_memLp Q a hEll i j) hw
  rw [hpoint,←cube_average_eq_volume_average_open,cubeAverage_eq_integral_normalizedCubeMeasure,
    integral_neg,integral_finsetSum Finset.univ (fun j _ => hi j)]


end
end ASDExplicitGamma.Native
