module

public import ASDExplicitGamma.Scalar.OldHessianTrialFlatCovarianceProfile
public import ASDExplicitGamma.Scalar.OldHessianTrialPhysicalScales
public import ASDExplicitGamma.Native.OldSignedQ1FlatConstants
public import ASDExplicitGamma.Numerics.Scalar.Lower

/-! Physical flat covariance coefficients at the original fine mesh. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main
open Numerics.Mirror Numerics.Scalar
noncomputable section

/-- The original covariance cap retains its actual boundary energy and
has exactly the physical .304 s1 coefficient. -/
theorem old_hessian_physical_flat_covariance_cap (m : ℤ) (b : ℝ) :
    oldHessianFlatCovarianceCap (originCube 2 (m+129)) 134 b (q3ModelLength (m+1))≤
      |b| *Real.sqrt (oldSignedFlatBoundaryEnergy (originCube 2 (m+129)) b (q3ModelLength (m+1))/2)+
        ((38/125:ℝ)*evalReal scalarRealEnv lowerS1Expr*|b|)*
          (Real.sqrt (oldSignedFlatBoundaryEnergy (originCube 2 (m+129)) b (q3ModelLength (m+1))/2)+2*|b|) := by
  let Q := originCube 2 (m+129)
  let L := q3ModelLength (m+1)
  let r := cubeScaleFactor Q/(3:ℝ)^134
  let T := Real.sqrt (oldSignedFlatBoundaryEnergy Q b L/2)
  have hs : Real.sqrt (mainFlatSigmaSq b L)=|b| *Real.sqrt (156/5:ℝ)/L.val := by
    have he : mainFlatSigmaSq b L=b^2*(156/5:ℝ)/L.val^2 := by unfold mainFlatSigmaSq; ring
    rw [he]
    rw [Real.sqrt_div (mul_nonneg (sq_nonneg b) (by norm_num)),
      Real.sqrt_mul (sq_nonneg b),Real.sqrt_sq_eq_abs,Real.sqrt_sq L.property.le]
  have hr : r/L.val=1/(3:ℝ)^6 := old_hessian_physical_mesh_ratio m 5
  have he : r*Real.sqrt (mainFlatSigmaSq b L)=|b| *evalReal scalarRealEnv lowerS1Expr := by
    rw [hs]
    calc
      _ = |b| *Real.sqrt (156/5:ℝ)*(r/L.val) := by ring
      _ = _ := by rw [hr]; norm_num [evalReal,lowerS1Expr,sc]; ring
  have hnon : 0≤r*(Real.sqrt (mainFlatSigmaSq b L)*T+2*|b| *Real.sqrt (mainFlatSigmaSq b L)) := by
    apply mul_nonneg (div_nonneg (Triadic.cubeScaleFactor_pos' Q).le (by positivity))
    exact add_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg b)) (Real.sqrt_nonneg _))
  have hC1 : planarC1≤(38/125:ℝ) := by convert old_signed_planarC1_le_304 using 1 <;> norm_num
  have hh := mul_le_mul_of_nonneg_right hC1 hnon
  change _≤|b| *T+_
  unfold oldHessianFlatCovarianceCap
  change |b| *T+r*planarC1*(Real.sqrt (mainFlatSigmaSq b L)*T+2*|b| *Real.sqrt (mainFlatSigmaSq b L))≤_
  calc
    _ = |b| *T+planarC1*(r*(Real.sqrt (mainFlatSigmaSq b L)*T+2*|b| *Real.sqrt (mainFlatSigmaSq b L))) := by ring
    _ ≤ |b| *T+(38/125:ℝ)*(r*(Real.sqrt (mainFlatSigmaSq b L)*T+2*|b| *Real.sqrt (mainFlatSigmaSq b L))) := add_le_add le_rfl hh
    _ = |b| *T+(38/125:ℝ)*(r*Real.sqrt (mainFlatSigmaSq b L))*(T+2*|b|) := by ring
    _ = _ := by rw [he]; ring

/-- Substitution of a deterministic boundary-energy cap into the original
flat covariance coefficient. The boundary estimate remains an explicit
input to this deterministic helper. -/
theorem old_hessian_physical_flat_covariance_of_boundary (m : ℤ) (b q : ℝ)
    (hq : 0≤q)
    (hboundary : oldSignedFlatBoundaryEnergy (originCube 2 (m+129)) b (q3ModelLength (m+1))≤b^2*q) :
    oldHessianFlatCovarianceCap (originCube 2 (m+129)) 134 b (q3ModelLength (m+1))≤
      b^2*(Real.sqrt (q/2)+((38/125:ℝ)*evalReal scalarRealEnv lowerS1Expr)*(Real.sqrt (q/2)+2)) := by
  have hroot : Real.sqrt (oldSignedFlatBoundaryEnergy (originCube 2 (m+129)) b (q3ModelLength (m+1))/2)≤
      |b| *Real.sqrt (q/2) := by
    have hh := Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hboundary (by norm_num : (0:ℝ)≤2))
    rw [mul_div_assoc,Real.sqrt_mul (sq_nonneg b),Real.sqrt_sq_eq_abs] at hh
    exact hh
  have hS : 0≤evalReal scalarRealEnv lowerS1Expr := by norm_num [evalReal,lowerS1Expr,sc]
  have hh := add_le_add (mul_le_mul_of_nonneg_left hroot (abs_nonneg b))
    (mul_le_mul_of_nonneg_left (add_le_add hroot (le_refl (2*|b|)))
      (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ)≤38/125) hS) (abs_nonneg b)))
  exact (old_hessian_physical_flat_covariance_cap m b).trans (hh.trans_eq (by rw [←sq_abs b]; ring))

end
end ASDExplicitGamma.Scalar
