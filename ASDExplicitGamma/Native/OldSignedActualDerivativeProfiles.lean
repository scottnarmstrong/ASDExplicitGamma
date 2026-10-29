module

public import ASDExplicitGamma.Native.OldSignedQ1DerivativePayment
public import ASDExplicitGamma.Native.OldSignedCellDerivativeBounds
public import ASDExplicitGamma.Native.OldSignedActualProxyCarrier

/-! Actual root-energy profiles for the complete OLD derivative block. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Algsuperdiff.Section3
noncomputable section

/-- All derivative factors use the same tiled weak energy and the exact
joint/minus/offset spatial proxies. No stochastic estimate is assumed. -/
theorem old_signed_actual_derivative_profile_bounds (M : ABKModel 2) (n : ℤ)
    (r : ℕ) (t : ℝ) (ht : 0≤t ∧ t≤1) (ω : Cutoff.CutoffSample 2)
    (b : ℝ) (L : {l : ℝ // 0<l}) :
    let Q := originCube 2 n
    let sigma : ℝ := Annealed.sigmaBar M n
    let hsigma := (Annealed.sigmaBar_characterization M n).1
    let k := oldSignedPartialResponseCoefficient n 1 t ω
    let G := fun (U : OldSignedCellIndex Q r) => oldSignedReciprocalErrorSize Q U.val M.nu sigma M.nu_pos hsigma k
    let d := fun (U : OldSignedCellIndex Q r) => oldSignedOldSourceSize Q U.val r M.nu sigma M.nu_pos hsigma k b L
    let p := fun (U : OldSignedCellIndex Q r) => Real.sqrt (oldSignedActualPlusMeanProxy M n r U.val U.property t b L ω)
    let q := fun (U : OldSignedCellIndex Q r) => Real.sqrt (oldSignedActualMinusMeanProxy M n r U.val U.property t b L ω)
    let e := fun (U : OldSignedCellIndex Q r) =>
      let H := oldSignedMaxTraceHistory U.val (oldSignedPartialFrameField M n 1 t ω)
      (Real.sqrt (rawShellBandLocalHistory M n 1 t ω*(1+2*H+Real.sqrt (2*H)))+1)*oldSignedFlatOscillationSize Q U.val b L false
    let W := oldSignedActualTiledWeakProxy M n r t ω
    Real.sqrt (oldSignedCellAverage Q r (fun U => G U^2))≤Real.sqrt (2*W) ∧
    Real.sqrt (oldSignedCellAverage Q r (fun U => d U^2))≤oldSignedSourceMultiplier Q r b L*Real.sqrt W ∧
    Real.sqrt (oldSignedCellAverage Q r (fun U => p U^2))≤Real.sqrt (oldSignedActualJointSpatialProxy M n r t b L ω) ∧
    Real.sqrt (oldSignedCellAverage Q r (fun U => q U^2))=Real.sqrt (oldSignedActualMinusSpatialProxy M n r t b L ω) ∧
    Real.sqrt (oldSignedCellAverage Q r (fun U => e U^2))=Real.sqrt (oldSignedActualReciprocalOffsetEnergy M n r t b L ω) := by
  intro Q sigma hsigma k G d p q e W
  have hp := old_signed_actual_tiled_profile_bounds M n r t ht ω b L
  have hG : oldSignedCellAverage Q r (fun U => G U^2)≤2*W := by
    rw [old_signed_cell_average_eq_descendantsAverage Q r
      (fun U => oldSignedReciprocalErrorSize Q U M.nu sigma M.nu_pos hsigma k^2)]
    apply le_trans _ hp.2.1
    unfold descendantsAverage
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
    exact Finset.sum_le_sum (fun U _ => le_add_of_nonneg_left (sq_nonneg _))
  have hd : oldSignedCellAverage Q r (fun U => d U^2)≤oldSignedSourceMultiplier Q r b L^2*W := by
    rw [old_signed_cell_average_eq_descendantsAverage Q r
      (fun U => oldSignedOldSourceSize Q U r M.nu sigma M.nu_pos hsigma k b L^2)]
    exact hp.2.2
  refine ⟨Real.sqrt_le_sqrt hG,old_signed_cell_root_cap Q r d _ W
    (old_signed_source_multiplier_nonneg Q r b L) hd,?_,?_,?_⟩
  · apply Real.sqrt_le_sqrt
    apply old_signed_cell_average_mono
    intro U
    change (Real.sqrt (oldSignedActualPlusMeanProxy M n r U.val U.property t b L ω))^2≤_
    rw [Real.sq_sqrt (old_signed_actual_plus_mean_proxy_nonneg M n r U.val U.property t b L ω)]
    exact le_add_of_nonneg_right (old_signed_actual_minus_mean_proxy_nonneg M n r U.val U.property t b L ω)
  · dsimp only [q]
    simp_rw [Real.sq_sqrt (old_signed_actual_minus_mean_proxy_nonneg M n r _ _ t b L ω)]
    rfl
  · dsimp only [e]
    simp_rw [mul_pow]
    rfl

end
end ASDExplicitGamma.Native
