module

public import ASDExplicitGamma.Native.OldSignedTopDirectionalWeakProxy

/-! Component bounds from the joint top-load directional energy. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Triadic
noncomputable section

/-- The first affine top-load defect is paid by the directional proxy. -/
theorem old_signed_top_first_weak_norm (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (e : Vec 2) :
    let S := oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (e,0)
    vectorWeakHaarNorm Q (fun x => (S x).1-e) ≤
      Real.sqrt (oldSignedDirectionalProxy Q (responseFramePlanarCoefficientField nu sigma k) e) := by
  intro S
  apply Real.sqrt_le_sqrt
  exact (le_add_of_nonneg_right (vectorWeakHaarEnergy_nonneg Q _)).trans
    (old_signed_top_directional_weak_bound Q nu sigma hnu hsigma k e)

/-- The reciprocal top-load field uses the same directional proxy. -/
theorem old_signed_top_reciprocal_weak_norm (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (e : Vec 2) :
    let S := oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (e,0)
    vectorWeakHaarNorm Q (fun x => (scalarCoefficientFlux
      (responseFramePlanarCoefficientField nu sigma k) S x).2) ≤
      Real.sqrt (oldSignedDirectionalProxy Q (responseFramePlanarCoefficientField nu sigma k) e) := by
  intro S
  apply Real.sqrt_le_sqrt
  exact (le_add_of_nonneg_left (vectorWeakHaarEnergy_nonneg Q _)).trans
    (old_signed_top_directional_weak_bound Q nu sigma hnu hsigma k e)

end
end ASDExplicitGamma.Native
