module

public import ASDExplicitGamma.Native.OldSignedCompleteOldErrorFeedback
public import ASDExplicitGamma.Native.OldSignedOldSourceBudget
public import ASDExplicitGamma.Native.OldSignedReciprocalLoadBudget

/-! The complete derivative-only OLD-source feedback term of AN (5.1),
with the actual four parent reciprocal loads and sharp source budget. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
noncomputable section

/-- The actual full four-load R feedback has the precise sharp local
bill kappa (sqrt(2)+G_U) D B_U d_U. Every input is physical source data. -/
theorem old_signed_actual_old_source_feedback_bill (m : ℤ) (mesh : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet (originCube 2 m)))
    (b : ℝ) (L : {l : ℝ // 0<l})
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 m) mesh) :
    let Q := originCube 2 m
    let hsub := openCubeSet_subset_of_mem_descendantsAtDepth hU
    let a := responseFramePlanarCoefficientField nu sigma k
    let kU := oldSignedCellCoefficient Q U hsub k
    let R := fun n c => oldSignedCellResidual Q U hsub nu sigma hnu hsigma k
      (oldSignedFrameOldErrorSource Q mesh nu sigma hnu hsigma k b L n (blockBasis c))
      (old_signed_frame_old_error_source_memL2 Q mesh nu sigma hnu hsigma k b L n (blockBasis c))
    let f := fun n => ∑ c : BlockCoord 2,oldSignedEnergyPairing U nu sigma kU
      (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (blockBasis c))
      (oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n)) (R n c))
    Summable f ∧ |∑' n,f n|≤oldSignedDerivativeKappa (cubeScaleFactor U) b L.1*
      (Real.sqrt 2+oldSignedReciprocalErrorSize Q U nu sigma hnu hsigma k)*
      ((1+inverseHistoryDiscount)*oldSignedInverseHistory U a*
        oldSignedOldSourceSize Q U mesh nu sigma hnu hsigma k b L) := by
  intro Q hsub a kU R f
  let v := fun n c => oldSignedCellErrorPotential Q U hsub mesh nu sigma hnu hsigma k b L n (blockBasis c)
  have hv (c : BlockCoord 2) : Summable (fun n : whiteBasisIndex =>
      vectorWeakHaarNorm U (v n c).toH1Function.grad^2) :=
    old_signed_old_error_cell_potential_summable m mesh nu sigma hnu hsigma k (blockBasis c) b L U hU
  have heq : (∑ c : BlockCoord 2,∑' n : whiteBasisIndex,vectorWeakHaarNorm U (v n c).toH1Function.grad^2)=
      ∑' n : whiteBasisIndex,∑ c : BlockCoord 2,vectorWeakHaarNorm U (v n c).toH1Function.grad^2 :=
    (Summable.tsum_finsetSum (fun c _ => hv c)).symm
  have hh := old_signed_complete_old_error_feedback m mesh nu sigma hnu hsigma k blockBasis b L U hU
  have hb := (old_signed_actual_old_source_budget m mesh nu sigma hnu hsigma k b L U hU).2.2.2
  have hg := old_signed_actual_reciprocal_load_budget Q U hsub nu sigma hnu hsigma k
  have hκ := old_signed_derivative_kappa_nonneg (Triadic.cubeScaleFactor_pos' U).le b L.1
  have hgnonneg : 0≤Real.sqrt 2+oldSignedReciprocalErrorSize Q U nu sigma hnu hsigma k :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hresult : Summable f ∧ |∑' n,f n|≤oldSignedDerivativeKappa (cubeScaleFactor U) b L.1*
      Real.sqrt (∑ c : BlockCoord 2,vectorWeakHaarNorm U
        (oldSignedCellReciprocalPotential Q U hsub nu sigma hnu hsigma k (blockBasis c)).grad^2)*
      Real.sqrt (∑ c : BlockCoord 2,∑' n : whiteBasisIndex,
        vectorWeakHaarNorm U (v n c).toH1Function.grad^2) := hh
  rw [heq] at hresult
  exact ⟨hresult.1,hresult.2.trans (mul_le_mul (mul_le_mul_of_nonneg_left hg hκ) hb
    (Real.sqrt_nonneg _) (mul_nonneg hκ hgnonneg))⟩

end
end ASDExplicitGamma.Native
