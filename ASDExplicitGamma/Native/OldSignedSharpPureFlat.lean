module

public import ASDExplicitGamma.Native.OldSignedSharpFlatAffine
public import ASDExplicitGamma.Native.OldSignedPhysicalFluxDirectionalNorm

/-! Sharp affine source-energy payment for either pure block mean. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Triadic
noncomputable section

/-- The complete OLD corrector history is nonnegative without any sign
condition on a partial-law inverse trace. -/
theorem old_signed_corrector_history_nonneg (Q : TriadicCube 2) (a : CoeffField 2) :
    0 ≤ oldSignedCorrectorHistory Q a := by
  unfold oldSignedCorrectorHistory oldSignedResponseHistory
  exact mul_nonneg (mul_nonneg (add_nonneg (by norm_num) inverse_history_discount_range.1.le)
    ENNReal.toReal_nonneg) ENNReal.toReal_nonneg

/-- The literal constant-input physical flux satisfies the sharp square-root
norm bound for either pure load. -/
theorem old_signed_pure_affine_flux_norm (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (bottom : Bool) (e : Vec 2) :
    let P := oldSignedDirectionalLoad bottom e
    oldSignedBlockWeakNorm Q (fun x => scalarCoefficientFlux
      (responseFramePlanarCoefficientField nu sigma k)
      (scalarResidualField Q nu sigma hnu hsigma k
        ((scalarFrameRealization Q nu sigma hnu hsigma k).constantField P)) x-P) ≤
      Real.sqrt (2*oldSignedCorrectorHistory Q (responseFramePlanarCoefficientField nu sigma k))*
        Real.sqrt (vecNormSq e) := by
  intro P
  rw [old_signed_affine_residual_field]
  have hh := old_signed_physical_flux_directional_weak_norm Q nu sigma hnu hsigma k bottom e
  have hΘ := old_signed_corrector_history_nonneg Q (responseFramePlanarCoefficientField nu sigma k)
  have hr : (Real.sqrt (2*oldSignedCorrectorHistory Q (responseFramePlanarCoefficientField nu sigma k))*
      Real.sqrt (vecNormSq e))^2=
      2*oldSignedCorrectorHistory Q (responseFramePlanarCoefficientField nu sigma k)*vecNormSq e := by
    rw [mul_pow,Real.sq_sqrt (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hΘ),
      Real.sq_sqrt (vecNormSq_nonneg e)]
  have hs := hh.trans_eq hr.symm
  exact (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp hs

/-- Actual flat-source energy with a pure block mean has the sharp physical
flux cross coefficient. Its flux estimate is proved here, not assumed. -/
theorem old_signed_flat_projection_energy_pure_mean
    (Q : TriadicCube 2) (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (F : Vec 2 → BlockVec 2)
    (hF : MemBlockL2 (openCubeSet Q) F) (bottom : Bool) (e : Vec 2)
    (hmean : oldSignedBlockMean Q F=oldSignedDirectionalLoad bottom e)
    (hPfst : ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3)^(j+1)*
      energy Q (cubeIncrement Q (j+1) (fun x => (F x).1 i-(oldSignedBlockMean Q F).1 i))))
    (hPsnd : ∀ i : Fin 2, Summable (fun j : ℕ => (Real.sqrt 3)^(j+1)*
      energy Q (cubeIncrement Q (j+1) (fun x => (F x).2 i-(oldSignedBlockMean Q F).2 i)))) :
    let a := responseFramePlanarCoefficientField nu sigma k
    oldSignedEnergyPairing Q nu sigma k
      (scalarResidualField Q nu sigma hnu hsigma k (toHilbertBlockL2OfBlockField hF))
      (scalarResidualField Q nu sigma hnu hsigma k (toHilbertBlockL2OfBlockField hF)) ≤
      blockVecDot (oldSignedBlockMean Q F)
        (blockMatVecMul (coarseBlockMatrix (openCubeSet Q) a) (oldSignedBlockMean Q F))+
      2*(Real.sqrt (2*oldSignedCorrectorHistory Q a)*Real.sqrt (vecNormSq e))*
        oldSignedBlockPositiveNorm Q (fun x => F x-oldSignedBlockMean Q F)+
      oldSignedResponseHistory Q a*(oldSignedBlockPositiveNorm Q (fun x => F x-oldSignedBlockMean Q F))^2 := by
  intro a
  apply old_signed_flat_projection_energy_of_flux_norm Q nu sigma hnu hsigma k F hF _ hPfst hPsnd
  rw [hmean]
  exact old_signed_pure_affine_flux_norm Q nu sigma hnu hsigma k bottom e

end
end ASDExplicitGamma.Native
