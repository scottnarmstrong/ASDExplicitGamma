module

public import ASDExplicitGamma.Native.OldSignedTopFlatPairing
public import ASDExplicitGamma.Native.OldSignedErrorBill

/-! The actual localized top-flat cross pairing has zero bulk and the
literal four-load betaPlus V_U covariance bill of AN (5.1). -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
noncomputable section

/-- Complete actual localized top-flat covariance is bounded by the
joint cell betaPlus times the actual four-parent-load primal error. -/
theorem old_signed_actual_top_covariance_bill (Q : TriadicCube 2) (mesh : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l}) :
    let f := fun n : whiteBasisIndex => 2*∑ i : Fin 2,volumeAverage (openCubeSet Q) (fun x =>
      vecDot (oldSignedFlatPlusBlock Q b L n i x).2
        (oldSignedFrameOldErrorSource Q mesh nu sigma hnu hsigma k b L n (basisVec i,0) x).2)
    Summable f ∧ |∑' n,f n|≤2*descendantsAverage Q mesh (fun U =>
      oldSignedCovarianceBeta Q U b L true*oldSignedPrimalErrorSize Q U nu sigma hnu hsigma k) := by
  intro f
  let a := responseFramePlanarCoefficientField nu sigma k
  let hEll := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
    nu sigma hnu hsigma k
  have hs := old_signed_actual_top_flat_hasSum Q mesh nu sigma hnu hsigma k b L
  have hb := old_signed_top_covariance_feedback Q mesh a hEll b L
  rw [(old_signed_top_flat_covariance Q a hEll b L).tsum_eq] at hb
  have hactual : |∑' n,f n|≤2*descendantsAverage Q mesh (fun U => oldSignedCovarianceBeta Q U b L true*
      Real.sqrt (∑ i : Fin 2,vectorWeakHaarNorm U (oldSignedTopPrimalError Q a hEll i)^2)) := by
    rw [hs.tsum_eq,abs_neg]
    exact hb
  refine ⟨hs.summable,hactual.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤2)
  unfold descendantsAverage
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  apply Finset.sum_le_sum
  intro U _
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  apply Real.sqrt_le_sqrt
  let v := fun c : BlockCoord 2 => vectorWeakHaarNorm U (fun x =>
    (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (blockBasis c) x).1-(blockBasis c).1)^2
  change (∑ i : Fin 2,v (Sum.inl i))≤∑ c : BlockCoord 2,v c
  rw [Fintype.sum_sum_type]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

end
end ASDExplicitGamma.Native
