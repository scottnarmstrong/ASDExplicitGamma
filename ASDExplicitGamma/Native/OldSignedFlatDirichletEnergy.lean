module

public import ASDExplicitGamma.Native.OldSignedHarmonicRemainder

/-! Actual finite-volume orthogonal subtraction for the minus boundary
remainder. These energy identities use the real Dirichlet projection. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Main
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Response
noncomputable section

/-- Every rotated source load has actual local L2 membership. -/
theorem old_signed_rotated_raw_load_memL2 (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (w : WhiteNoise) (i : Fin 2) :
    MemVectorL2 (openCubeSet Q) (fun x =>
      q3Convolution b L h3Zero w x • mainFlatRotatedBasis i) := by
  let u := H1Function.ofContDiffOnIsOpenBoundedConvexDomain (isOpenBoundedConvexDomain_openCubeSet Q)
    (q3Convolution_contDiff_one b L h3Zero (by norm_num [h3Zero,H3Index]) w)
  exact ((ContinuousLinearMap.id ℝ ℝ).smulRight (mainFlatRotatedBasis i)).comp_memLp' u.memL2

/-- The source minus field is the local Dirichlet projection of the actual
whole-plane rotated-input field, on the same square and white realization. -/
theorem old_signed_flat_minus_is_dirichlet_projection (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) (i : Fin 2) :
    toHilbertVectorL2OfVecField (old_signed_flat_minus_memL2 Q b L n i)=
      lambda8DirichletProjection (isOpenBoundedConvexDomain_openCubeSet Q)
        (toHilbertVectorL2OfVecField (old_signed_rotated_projected_memL2 Q b L (whiteBasis n) i)) := by
  have hraw := old_signed_rotated_raw_load_memL2 Q b L (whiteBasis n) i
  have he := old_signed_dirichlet_projection_eq_of_solenoidal
    (isOpenBoundedConvexDomain_openCubeSet Q) hraw
    (old_signed_rotated_projected_memL2 Q b L (whiteBasis n) i)
    (old_signed_rotated_projected_residual_solenoidal Q b L (whiteBasis n) i)
  rw [←he]
  have hs := (lambda8Q3GaussianModeParentPotential_spec Q b L (mainFlatRotatedBasis i) n).1
  have hfam : toHilbertVectorL2OfVecField hraw=
      toHilbertVectorL2OfVecField (lambda8H1ComponentField_memVectorL2
        (fun k => lambda8Q3GaussianModeLoadH1 Q b L (mainFlatRotatedBasis i) n k)) := by
    apply Lp.ext
    filter_upwards [coeFn_toHilbertVectorL2OfVecField hraw,
      coeFn_toHilbertVectorL2OfVecField (lambda8H1ComponentField_memVectorL2
        (fun k => lambda8Q3GaussianModeLoadH1 Q b L (mainFlatRotatedBasis i) n k))] with x hx hy
    rw [hx,hy]
    rfl
  rw [hfam,hs]
  have hf : (fun x k => mainFlatMinusCoordinate Q b L n (i,k) x)=
      (lambda8Q3GaussianModeParentPotential Q b L (mainFlatRotatedBasis i) n).toH1Function.grad := by
    funext x k
    exact old_signed_flat_minus_coordinate Q b L n i k x
  apply Lp.ext
  filter_upwards [coeFn_toHilbertVectorL2OfVecField (old_signed_flat_minus_memL2 Q b L n i),
    (lambda8Q3GaussianModeParentPotential Q b L (mainFlatRotatedBasis i) n).toH1Function.coeFn_gradToHilbertVectorL2]
      with x hx hy
  rw [hx,hy]
  exact congrArg HilbertVec.ofVec (congrFun hf x)

/-- Per actual white mode and load, the negative harmonic remainder has
exactly the projected energy not retained by the local Dirichlet projection. -/
theorem old_signed_flat_minus_energy_subtraction (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) (i : Fin 2) :
    ‖toHilbertVectorL2OfVecField (old_signed_rotated_projected_memL2 Q b L (whiteBasis n) i)‖^2 =
      ‖toHilbertVectorL2OfVecField (old_signed_flat_minus_memL2 Q b L n i)‖^2+
        ‖toHilbertVectorL2OfVecField (old_signed_flat_remainders_memL2 Q b L n i).2‖^2 := by
  let hQ := isOpenBoundedConvexDomain_openCubeSet Q
  let V := toHilbertVectorL2OfVecField (old_signed_rotated_projected_memL2 Q b L (whiteBasis n) i)
  have hh := (lambda8H10GradientRange hQ).toSubmodule.norm_sq_eq_add_norm_sq_starProjection V
  rw [Submodule.starProjection_orthogonal_val] at hh
  change ‖V‖^2=‖lambda8DirichletProjection hQ V‖^2+‖V-lambda8DirichletProjection hQ V‖^2 at hh
  rw [←old_signed_flat_minus_is_dirichlet_projection] at hh
  have he : toHilbertVectorL2OfVecField (old_signed_flat_remainders_memL2 Q b L n i).2=
      toHilbertVectorL2OfVecField (old_signed_flat_minus_memL2 Q b L n i)-V :=
    toHilbertVectorL2OfVecField_sub (old_signed_flat_minus_memL2 Q b L n i)
      (old_signed_rotated_projected_memL2 Q b L (whiteBasis n) i)
  rw [he]
  simpa only [norm_sub_rev] using hh

end
end ASDExplicitGamma.Native
