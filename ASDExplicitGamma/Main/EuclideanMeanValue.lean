module

public import ASDExplicitGamma.Main.RankOneMultiplier
public import Mathlib.Analysis.Calculus.MeanValue

/-! Mean value bounds retaining the Euclidean spatial metric on planar function coordinates. -/

@[expose] public section
namespace ASDExplicitGamma.Main
open Homogenization
open scoped BigOperators

/-- Squared Euclidean distance, independently of the sup norm on `Vec 2`. -/
def mainSpatialDistanceSq (x y : Vec 2) : ℝ := ∑ i, (x i-y i)^2

/-- A derivative bound in the Euclidean spatial metric integrates along the
actual line segment with no sup-norm dimension factor. -/
theorem main_euclidean_mean_value {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : Vec 2 → F} (hf : Differentiable ℝ f)
    {G : ℝ} (hG : 0 ≤ G)
    (hd : ∀ x v, ‖(fderiv ℝ f x) v‖^2 ≤ G^2*mainSpatialDistanceSq v 0)
    (x y : Vec 2) : ‖f x-f y‖^2 ≤ G^2*mainSpatialDistanceSq x y := by
  let z : ℝ → Vec 2 := fun t => y+t • (x-y)
  let C := G*Real.sqrt (mainSpatialDistanceSq x y)
  have hN : 0 ≤ mainSpatialDistanceSq x y := Finset.sum_nonneg fun i _ => sq_nonneg _
  have he : mainSpatialDistanceSq (x-y) 0 = mainSpatialDistanceSq x y := by
    simp only [mainSpatialDistanceSq, Pi.sub_apply, Pi.zero_apply, sub_zero]
  have hz (t : ℝ) : HasDerivAt z (x-y) t := by
    simpa only [one_smul, id_eq, z] using
      ((hasDerivAt_id t).smul_const (x-y)).const_add y
  have hder (t : ℝ) : HasDerivAt (fun t => f (z t)) ((fderiv ℝ f (z t)) (x-y)) t :=
    (hf (z t)).hasFDerivAt.comp_hasDerivAt t (hz t)
  have hbound (t : ℝ) : ‖(fderiv ℝ f (z t)) (x-y)‖ ≤ C := by
    have h := hd (z t) (x-y)
    rw [he] at h
    apply (Real.le_sqrt (norm_nonneg _) (mul_nonneg (sq_nonneg G) hN)).2 at h
    simpa only [Real.sqrt_mul (sq_nonneg G), Real.sqrt_sq hG, C] using h
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ => (hder t).hasDerivWithinAt) (fun t _ => hbound t)
  have hxy : ‖f x-f y‖ ≤ C := by
    simpa only [z, one_smul, zero_smul, add_zero, add_sub_cancel] using h
  have hs := pow_le_pow_left₀ (norm_nonneg _) hxy 2
  simpa only [C, mul_pow, Real.sq_sqrt hN] using hs

end ASDExplicitGamma.Main
