module

public import ASDExplicitGamma.Native.ParentRowDerivativeProfiles
public import ASDExplicitGamma.Native.OldSignedDerivativeCellMajorant
public import ASDExplicitGamma.Native.OldSignedDerivativeEnvelopeIdentity

/-! The complete literal AN derivative feedback is paid by its actual-law envelope. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Triadic Algsuperdiff.Section3
noncomputable section

/-- Expanded derivative envelope; all seven random factors belong to the
same actual law, including the bank-weighted weak terms. -/
def parentRowDerivativeEnvelope (M : ABKModel 2) (n : ℤ) (height r : ℕ)
    (t b : ℝ) (L : {l : ℝ // 0<l}) (ω : Cutoff.CutoffSample 2) : ℝ :=
  let Q := originCube 2 n
  let kd := oldSignedDerivativeKappa (cubeScaleFactor Q/3^r) b L.1
  let ka := parentBoundaryPotentialSourceClock Q r b L
  let op := Real.sqrt (descendantsAverage Q r (fun U => oldSignedFlatOscillationSize Q U b L true^2))
  let W := parentBoundaryBandWeakProxy M n height r t ω
  let B := (nativeSourceBandHistory M n height t ω).toReal
  let J := parentBoundaryBandJointSpatialProxy M n height r t b L ω
  let N := parentRowMinusSpatialProxy M n height r t b L ω
  let E := parentRowReciprocalOffsetEnergy M n height r t b L ω
  (2*kd*Real.sqrt 2)*(Real.sqrt W*Real.sqrt J+Real.sqrt W*Real.sqrt N+Real.sqrt W*Real.sqrt E+
    ((1+inverseHistoryDiscount)*(op+ka))*(B*Real.sqrt W)+
    ((1+inverseHistoryDiscount)*ka)*(B*W)+Real.sqrt N+Real.sqrt E)

/-- All three physical derivative feedback terms are below the paid common
envelope almost surely. The later-shear OLD-source and reciprocal offsets
are both retained. -/
theorem parent_row_actual_derivative_spatial_majorant
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ) (height : ℕ)
    (hpast : ∀ l<n,nativeInductionState M h l) (r : ℕ) (hr : r≤5)
    (t : ℝ) (ht : 0≤t ∧ t≤1) (b : ℝ) (L : {l : ℝ // 0<l}) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      let Q := originCube 2 n
      let sigma : ℝ := Annealed.sigmaBar M n
      let hsigma := (Annealed.sigmaBar_characterization M n).1
      let k := pureFluxOpenResponseRestriction n (nativeSourceBandScalar n height t ω)
      let a := parentBoundaryBandFrameField M n height t ω
      let D := 1+inverseHistoryDiscount
      descendantsAverage Q r (fun U =>
        let G := oldSignedReciprocalErrorSize Q U M.nu sigma M.nu_pos hsigma k
        let d := parentBoundaryCellSourceSize Q U M.nu sigma M.nu_pos hsigma k b L
        let B := oldSignedInverseHistory U a
        let A := oldSignedResponseHistory U a
        let kd := oldSignedDerivativeKappa (cubeScaleFactor U) b L.1
        2*(kd*G*(Real.sqrt (oldSignedFlatDirectionalMeanProxy Q U a b L true)+D*B*oldSignedFlatOscillationSize Q U b L true))+
        2*(kd*(Real.sqrt 2+G)*(D*B*d))+
        2*(kd*(Real.sqrt 2+G)*(Real.sqrt (oldSignedFlatDirectionalMeanProxy Q U a b L false)+
          (Real.sqrt (B*A)+1)*oldSignedFlatOscillationSize Q U b L false)))≤
        parentRowDerivativeEnvelope M n height r t b L ω := by
  let Q := originCube 2 n
  have hall := parent_row_cell_inverse_history M h hM hg n height hpast r hr t ht.2
  filter_upwards [hall] with ω hω
  dsimp only
  let a := parentBoundaryBandFrameField M n height t ω
  let B := (nativeSourceBandHistory M n height t ω).toReal
  let D := 1+inverseHistoryDiscount
  let kd := oldSignedDerivativeKappa (cubeScaleFactor Q/3^r) b L.1
  let ka := parentBoundaryPotentialSourceClock Q r b L
  let H := fun (U : OldSignedCellIndex Q r) => oldSignedMaxTraceHistory U.val a
  let A := fun U => 1+2*H U+Real.sqrt (2*H U)
  let G := fun (U : OldSignedCellIndex Q r) => oldSignedReciprocalErrorSize Q U.val M.nu (Annealed.sigmaBar M n)
    M.nu_pos (Annealed.sigmaBar_characterization M n).1 (pureFluxOpenResponseRestriction n (nativeSourceBandScalar n height t ω))
  let d := fun (U : OldSignedCellIndex Q r) => parentBoundaryCellSourceSize Q U.val M.nu (Annealed.sigmaBar M n)
    M.nu_pos (Annealed.sigmaBar_characterization M n).1 (pureFluxOpenResponseRestriction n (nativeSourceBandScalar n height t ω)) b L
  let p := fun (U : OldSignedCellIndex Q r) => Real.sqrt (oldSignedFlatDirectionalMeanProxy Q U.val a b L true)
  let q := fun (U : OldSignedCellIndex Q r) => Real.sqrt (oldSignedFlatDirectionalMeanProxy Q U.val a b L false)
  let op := fun (U : OldSignedCellIndex Q r) => oldSignedFlatOscillationSize Q U.val b L true
  let om := fun (U : OldSignedCellIndex Q r) => oldSignedFlatOscillationSize Q U.val b L false
  let e := fun U => (Real.sqrt (B*A U)+1)*om U
  let W := parentBoundaryBandWeakProxy M n height r t ω
  let J := parentBoundaryBandJointSpatialProxy M n height r t b L ω
  let N := parentRowMinusSpatialProxy M n height r t b L ω
  let E := parentRowReciprocalOffsetEnergy M n height r t b L ω
  let O := Real.sqrt (descendantsAverage Q r (fun U => oldSignedFlatOscillationSize Q U b L true^2))
  have hD : 0≤D := add_nonneg (by norm_num) inverse_history_discount_range.1.le
  have hkd : 0≤kd := old_signed_q1_derivative_kappa_nonneg _ _ _
    (div_nonneg (Triadic.cubeScaleFactor_pos' Q).le (by positivity))
  have hprof := parent_row_derivative_profile_bounds M n height r t ω b L
  have hop : Real.sqrt (oldSignedCellAverage Q r (fun U => op U^2))≤O := by
    rw [old_signed_cell_average_eq_descendantsAverage Q r
      (fun U => oldSignedFlatOscillationSize Q U b L true^2)]
  have hbase := old_signed_cell_derivative_feedback_bound Q r G d p q op e kd (D*B)
    (Real.sqrt (2*W)) (ka*Real.sqrt W) (Real.sqrt J) (Real.sqrt N) O (Real.sqrt E)
    hkd (mul_nonneg hD ENNReal.toReal_nonneg) (Real.sqrt_nonneg _)
    hprof.1 hprof.2.1 hprof.2.2.1 hprof.2.2.2.1.le hop hprof.2.2.2.2.le
  have hfinal := hbase.trans_eq (old_signed_derivative_envelope_identity W kd ka D B O J N E
    (parent_row_weak_proxy_nonneg M n height r t ω))
  change oldSignedCellAverage Q r _≤parentRowDerivativeEnvelope M n height r t b L ω at hfinal
  rw [←old_signed_cell_average_eq_descendantsAverage]
  refine (old_signed_cell_average_mono Q r (fun U => ?_)).trans hfinal
  rw [cubeScaleFactor_descendant_eq_div_pow U.property]
  have hm := (parent_boundary_band_matrix_history_bounds M n height r U.val U.property t ω).1
  exact old_signed_derivative_cell_majorant (oldSignedInverseHistory U.val a) (oldSignedResponseHistory U.val a)
    B (A U) (G U) (d U) _ _ (op U) (om U) D kd
    (lemmaVInverseHistory_nonneg U.val a (Real.one_lt_rpow (by norm_num) (by norm_num)))
    ENNReal.toReal_nonneg (hω U.val U.property) hm (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hD hkd

end
end ASDExplicitGamma.Native
