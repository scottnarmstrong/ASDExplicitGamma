module

public import ASDExplicitGamma.Native.OldSignedFlatGaugePairing
public import ASDExplicitGamma.Native.OldSignedTopFlatCovariance

/-! Actual localized plus-flat pairings recover the physical signed
covariance after the proved global zero-normal gauge cancellation. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Main ASDExplicitGamma.Triadic
noncomputable section

/-- Exact signed quarter-turn identity for the physical flat pairing. -/
theorem old_signed_rotated_flat_pairing (e v : Vec 2) (t : ℝ) :
    vecDot (-v) (-(t • matVecMul responsePlanarJ e))=
      -(∑ j : Fin 2,e j*t*matVecMul responsePlanarJ v j) := by
  simp [vecDot,matVecMul,responsePlanarJ,Fin.sum_univ_two]
  ring

/-- One actual localized top-load flat pairing is the negative physical
covariance pairing used by the complete bulk cancellation. -/
theorem old_signed_actual_top_flat_pairing (Q : TriadicCube 2) (mesh : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0<l}) (n : whiteBasisIndex) (i : Fin 2) :
    let a := responseFramePlanarCoefficientField nu sigma k
    let hEll := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
      nu sigma hnu hsigma k
    volumeAverage (openCubeSet Q) (fun x =>
      vecDot (oldSignedFlatPlusBlock Q b L n i x).2
        (oldSignedFrameOldErrorSource Q mesh nu sigma hnu hsigma k b L n (basisVec i,0) x).2)=
    -(∑ j : Fin 2,∫ x,oldSignedTopPrimalError Q a hEll i x j*
      q3Convolution b L h3Zero (whiteBasis n) x*
      matVecMul responsePlanarJ (fun l => mainFlatPlusCoordinate Q b L n (i,l) x) j
        ∂normalizedCubeMeasure Q) := by
  intro a hEll
  rw [old_signed_actual_plus_flat_gauge_pairing Q mesh nu sigma hnu hsigma k (basisVec i,0) b L n i]
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

/-- The complete actual localized top-flat pairings have exactly the
negative harmonic covariance value; their constant bulk cancels pathwise. -/
theorem old_signed_actual_top_flat_hasSum (Q : TriadicCube 2) (mesh : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l}) :
    let a := responseFramePlanarCoefficientField nu sigma k
    let hEll := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
      nu sigma hnu hsigma k
    HasSum (fun n : whiteBasisIndex => 2*∑ i : Fin 2,volumeAverage (openCubeSet Q) (fun x =>
      vecDot (oldSignedFlatPlusBlock Q b L n i x).2
        (oldSignedFrameOldErrorSource Q mesh nu sigma hnu hsigma k b L n (basisVec i,0) x).2))
      (-(2*∑ i : Fin 2,∑ j : Fin 2,∫ x,oldSignedTopPrimalError Q a hEll i x j*
        oldSignedRemainderCovarianceField Q b L true i x j ∂normalizedCubeMeasure Q)) := by
  intro a hEll
  apply (old_signed_top_flat_covariance Q a hEll b L).neg.congr_fun
  intro n
  simp_rw [old_signed_actual_top_flat_pairing Q mesh nu sigma hnu hsigma k b L n,
    Finset.sum_neg_distrib]
  ring

end
end ASDExplicitGamma.Native
