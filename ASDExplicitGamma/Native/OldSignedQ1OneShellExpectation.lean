module

public import ASDExplicitGamma.Native.OldSignedDirectionalModelGenerator
public import ASDExplicitGamma.Native.OldSignedAffineExpectation
public import ASDExplicitGamma.Native.GenericSourceBandMeanHeat
public import ASDExplicitGamma.Native.ParentBoundaryInverseBandDrift
public import ASDExplicitGamma.Native.OldSignedQ1AffinePayment
public import ASDExplicitGamma.Native.OldSignedErrorSpatialMajorant

/-! The actual one-shell OLD generator expectation, consuming the exact
q1 affine payment and its sharp partition aggregation. -/

@[expose] public section
namespace ASDExplicitGamma.Native

open Homogenization MeasureTheory Response Scalar Gaussian Triadic Main Inverse Cold Variational
  Algsuperdiff.Section3

noncomputable section

/-- Restriction to the open cube and normalization identify the physical
closed-cube coarse matrix in its true scalar frame. -/
theorem old_signed_open_coarse_frame' (n : ℤ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (x : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    coarseBlockMatrix (openCubeSet (originCube 2 n))
      (responseFramePlanarCoefficientField nu sigma
        (pureFluxOpenResponseRestriction n x)) =
      frameMatrix sigma (coarseBlockMatrix (cubeSet (originCube 2 n))
        (responsePlanarCoefficientField nu
          (ContinuousMap.linearIsometryBoundedOfCompact _ ℝ ℝ x))) := by
  rw [coarseBlockMatrix_congr_of_ae_eq
    (pureFluxOpenResponseRestriction_frame_ae n nu sigma x hsigma)]
  rw [← cold_coarse_cube_open (originCube 2 n)]
  exact cold_coarse_frame hnu
    (responsePlanarCoefficientField_isElliptic
      (measurableSet_cubeSet (originCube 2 n)) nu hnu
      (ContinuousMap.linearIsometryBoundedOfCompact _ ℝ ℝ x)) hsigma

/-- The retained inverse trace is the exact observable used by the
height-one inverse return. -/
theorem old_signed_q1_inverse_observable (M : ABKModel 2) (n : ℤ)
    (t : ℝ) (omega : Cutoff.CutoffSample 2) :
    Matrix.trace (coarseBlockMatrix (openCubeSet (originCube 2 n))
      (oldSignedPartialFrameField M n 1 t omega)).lowerRight =
      mainInverseObservable n M.nu (Annealed.sigmaBar M n)
        (nativeSourceBandScalar n 1 t omega) := by
  rw [← old_signed_single_band_frame]
  unfold parentBoundaryBandFrameField
  rw [old_signed_open_coarse_frame' n M.nu
    (Annealed.sigmaBar M n) M.nu_pos
    (Annealed.sigmaBar_characterization M n).1]
  simp only [frameMatrix, mainInverseObservable, Matrix.trace_smul, smul_eq_mul]

/-- The height-one actual source generator obeys the signed AN bound at its
physical amplitude and shell length. -/
theorem old_signed_q1_generator_pointwise (M : ABKModel 2) (h : ℝ)
    (n : ℤ) (r : ℕ) (t : ℝ) (omega : Cutoff.CutoffSample 2) :
    let Q := originCube 2 n
    let b := q3ModelAmplitude M h (n + 1) / (Annealed.sigmaBar M n : ℝ)
    let L := q3ModelLength (n + 1)
    nativeSourceBandMeanGenerator M h n 1 t omega ≤
      oldSignedFlatBoundaryEnergy Q b L +
        oldSignedFlatAffineContribution Q r
          (oldSignedPartialFrameField M n 1 t omega) b L -
        b ^ 2 * (mainInverseObservable n M.nu (Annealed.sigmaBar M n)
          (nativeSourceBandScalar n 1 t omega) - 2) +
        descendantsAverage Q r (fun U =>
          oldSignedDirectionalCellError Q U r M.nu (Annealed.sigmaBar M n)
            M.nu_pos (Annealed.sigmaBar_characterization M n).1
            (oldSignedPartialResponseCoefficient n 1 t omega) b L) := by
  intro Q b L
  have hraw := native_boundary_old_signed_model_generator_directional n r
    M.nu (Annealed.sigmaBar M n) M.nu_pos
    (Annealed.sigmaBar_characterization M n).1
    (nativeSourceBandScalar n 1 t omega) b L
  have hamp : (Annealed.sigmaBar M n : ℝ) * b =
      q3ModelAmplitude M h (n + 1) := by
    dsimp only [b]
    field_simp [(Annealed.sigmaBar_characterization M n).1.ne']
  have hcoeff : pureFluxOpenResponseRestriction n
      (nativeSourceBandScalar n 1 t omega) =
      oldSignedPartialResponseCoefficient n 1 t omega := by
    simp only [old_signed_single_band_scalar, oldSignedPartialResponseCoefficient,
      Nat.cast_one, add_sub_cancel_right]
  dsimp only at hraw
  rw [hamp, hcoeff] at hraw
  change _ ≤ oldSignedFlatBoundaryEnergy Q b L +
      oldSignedFlatAffineContribution Q r
        (oldSignedPartialFrameField M n 1 t omega) b L -
      b ^ 2 * (Matrix.trace (coarseBlockMatrix (openCubeSet Q)
        (oldSignedPartialFrameField M n 1 t omega)).lowerRight - 2) + _ at hraw
  rw [old_signed_q1_inverse_observable] at hraw
  simpa only [nativeSourceBandMeanGenerator, Fin.sum_univ_one,
    Nat.cast_one, Fin.val_zero, Nat.zero_add] using hraw

/-- The exact affine coefficient carried by the q1 source panel. -/
def oldSignedQ1AffineCap' (M : ABKModel 2) (n : ℤ) (t b : ℝ)
    (L : {l : ℝ // 0 < l}) : ℝ :=
  (b ^ 2 / 2) * (theta M * oldSignedQ1PanelMean t) +
    2 * b ^ 2 * ((3683 / 2500 : ℝ) - 1) +
    (4 + 2 * Real.sqrt 2) * (31.2 : ℝ) *
      ((cubeScaleFactor (originCube 2 n) / 3 ^ 5) ^ 2 * b ^ 2 / L.val ^ 2) / 9

/-- The actual one-shell source generator expectation with its complete
signed affine, inverse-trace and spatial-error bills. The affine payment
already incorporates the sharp partition mean-loss aggregation. -/
theorem old_signed_q1_generator_expectation'
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ)
    (hpast : ∀ l ≤ n, nativeInductionState M h l)
    (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) :
    let b := q3ModelAmplitude M h (n + 1) / (Annealed.sigmaBar M n : ℝ)
    let L := q3ModelLength (n + 1)
    (∫ omega, nativeSourceBandMeanGenerator M h n 1 t omega
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      oldSignedFlatBoundaryEnergy (originCube 2 n) b L +
        oldSignedQ1AffineCap' M n t b L -
        b ^ 2 * (parentBoundaryBandInverseMean M n 1 t - 2) +
        oldSignedQ1ErrorCap M n t b L := by
  intro b L
  let mu := (Cutoff.cutoffSampleLaw M).toMeasure
  let F := fun omega => oldSignedFlatAffineContribution (originCube 2 n) 5
    (oldSignedPartialFrameField M n 1 t omega) b L
  let D := fun omega => mainInverseObservable n M.nu
    (Annealed.sigmaBar M n) (nativeSourceBandScalar n 1 t omega)
  let E := oldSignedActualErrorEnvelope M n 5 t b L
  let B := oldSignedFlatBoundaryEnergy (originCube 2 n) b L
  have hF : Integrable F mu := (old_signed_affine_expectation M h hM n 5 t b L).1
  have hD : Integrable D mu :=
    (parent_boundary_inverse_band_integrable M h hM hg n 1
      (fun l hl => hpast l hl.le) t ht.2).1
  have hE := old_signed_q1_error_majorant M h hM hg n hpast t ht b L
  have hBF : Integrable (fun omega => B + F omega) mu :=
    (integrable_const B).add hF
  have hBD : Integrable (fun omega => b ^ 2 * (D omega - 2)) mu :=
    (hD.sub (integrable_const 2)).const_mul (b ^ 2)
  have hbase : Integrable (fun omega => B + F omega - b ^ 2 * (D omega - 2)) mu :=
    hBF.sub hBD
  have hbound := integral_mono_ae
    (native_source_band_mean_generator_integrable M h hM n 1 (by norm_num) t)
    (hbase.add hE.1)
    (show ∀ᵐ omega ∂mu,
      nativeSourceBandMeanGenerator M h n 1 t omega ≤
        B + F omega - b ^ 2 * (D omega - 2) + E omega from by
      filter_upwards [hE.2.2] with omega he
      exact (old_signed_q1_generator_pointwise M h n 5 t omega).trans
        (add_le_add (le_refl _) he))
  simp only [Pi.add_apply] at hbound
  rw [integral_add hbase hE.1, integral_sub hBF hBD,
    integral_add (integrable_const B) hF, integral_const_mul,
    integral_sub hD (integrable_const 2)] at hbound
  have hB : (∫ _ : Cutoff.CutoffSample 2, B ∂mu) = B := by simp
  have htwo : (∫ _ : Cutoff.CutoffSample 2, (2 : ℝ) ∂mu) = 2 := by simp
  rw [hB, htwo] at hbound
  have hpay : (∫ omega, F omega ∂mu) ≤ oldSignedQ1AffineCap' M n t b L :=
    old_signed_q1_affine_payment M h hM hg n hpast t ht b L
  have hDmean : (∫ omega, D omega ∂mu) =
      parentBoundaryBandInverseMean M n 1 t := rfl
  rw [hDmean] at hbound
  exact hbound.trans
    (add_le_add
      (sub_le_sub_right (add_le_add (le_refl B) hpay) _)
      hE.2.1)

end
end ASDExplicitGamma.Native
