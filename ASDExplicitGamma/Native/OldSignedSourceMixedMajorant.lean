module

public import ASDExplicitGamma.Native.OldSignedQ1SourceMixedPayment
public import ASDExplicitGamma.Native.OldSignedActualProxyCarrier

/-! The actual AN mixed-source block is dominated by the paid common-bank envelope. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Algsuperdiff.Section3
noncomputable section

/-- Monotonicity of the local quadratic/mixed block in its two history
multipliers; the joint affine energy remains unchanged. -/
theorem old_signed_source_mixed_cell_majorant
    (B₀ A₀ B A d P op om : ℝ) (hB₀ : 0≤B₀) (hA₀ : 0≤A₀)
    (hd : 0≤d) (hB : B₀≤B) (hA : A₀≤A) :
    B₀*d^2+2*(d*(Real.sqrt P+Real.sqrt ((B₀+1)^2*op^2+B₀*A₀*om^2)))≤
      B*d^2+2*(d*(Real.sqrt P+Real.sqrt ((B+1)^2*op^2+B*A*om^2))) := by
  have hBA := mul_le_mul hB hA hA₀ (hB₀.trans hB)
  have hoff := pow_le_pow_left₀ (add_nonneg hB₀ (by norm_num : (0:ℝ)≤1)) (add_le_add hB (le_refl (1:ℝ))) 2
  have he := add_le_add (mul_le_mul_of_nonneg_right hoff (sq_nonneg op))
    (mul_le_mul_of_nonneg_right hBA (sq_nonneg om))
  exact add_le_add (mul_le_mul_of_nonneg_right hB (sq_nonneg d))
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
      (add_le_add (le_refl (Real.sqrt P)) (Real.sqrt_le_sqrt he)) hd) (by norm_num))

/-- Actual OLD source mixed terms admit the integrable common-bank envelope
almost surely. The bank comparison, every matrix bound and all physical
proxy identifications are proved here from source inputs. -/
theorem old_signed_actual_source_mixed_majorant
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ)
    (hpast : ∀ l<n,nativeInductionState M h l) (r : ℕ) (hr : r≤5)
    (t : ℝ) (ht : 0≤t ∧ t≤1) (b : ℝ) (L : {l : ℝ // 0<l}) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      let Q := originCube 2 n
      let sigma : ℝ := Annealed.sigmaBar M n
      let hsigma := (Annealed.sigmaBar_characterization M n).1
      let k := oldSignedPartialResponseCoefficient n 1 t ω
      let a := oldSignedPartialFrameField M n 1 t ω
      let d := fun U => oldSignedOldSourceSize Q U r M.nu sigma M.nu_pos hsigma k b L
      descendantsAverage Q r (fun U =>
        oldSignedInverseHistory U a*d U^2+
          2*(d U*(Real.sqrt (oldSignedFlatDirectionalMeanProxy Q U a b L true+
            oldSignedFlatDirectionalMeanProxy Q U a b L false)+
            Real.sqrt ((oldSignedInverseHistory U a+1)^2*oldSignedFlatOscillationSize Q U b L true^2+
              oldSignedInverseHistory U a*oldSignedResponseHistory U a*oldSignedFlatOscillationSize Q U b L false^2))))≤
        oldSignedActualSourceMixedEnvelope M n r t b L ω := by
  let Q := originCube 2 n
  have hi (U : OldSignedCellIndex Q r) := old_signed_actual_cell_inverse_history_split
    M h hM hg n hpast r hr U.val U.property t ht
  have hall : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ∀ U : OldSignedCellIndex Q r,oldSignedInverseHistory U.val (oldSignedPartialFrameField M n 1 t ω)≤
        rawShellBandLocalHistory M n 1 t ω :=
    Filter.eventually_all.mpr (fun U => (hi U).mono (fun _ hh => hh.1))
  filter_upwards [hall] with ω hω
  dsimp only
  let a := oldSignedPartialFrameField M n 1 t ω
  let d := fun U => oldSignedOldSourceSize Q U r M.nu (Annealed.sigmaBar M n) M.nu_pos
    (Annealed.sigmaBar_characterization M n).1 (oldSignedPartialResponseCoefficient n 1 t ω) b L
  rw [←old_signed_cell_average_eq_descendantsAverage]
  apply le_trans (old_signed_cell_average_mono Q r (fun U => ?_))
    ((old_signed_actual_source_mixed_spatial_bound M n r t ht ω b L).trans_eq ?_)
  · unfold oldSignedActualSourceMixedEnvelope
    ring
  · have hm := (old_signed_actual_matrix_history_bounds M n r U.val U.property t ht ω).1
    have hh := old_signed_source_mixed_cell_majorant
      (oldSignedInverseHistory U.val a) (oldSignedResponseHistory U.val a)
      (rawShellBandLocalHistory M n 1 t ω) _ (d U.val)
      (oldSignedFlatDirectionalMeanProxy Q U.val a b L true+oldSignedFlatDirectionalMeanProxy Q U.val a b L false)
      (oldSignedFlatOscillationSize Q U.val b L true) (oldSignedFlatOscillationSize Q U.val b L false)
      (lemmaVInverseHistory_nonneg U.val a (Real.one_lt_rpow (by norm_num) (by norm_num)))
      ENNReal.toReal_nonneg (Real.sqrt_nonneg _) (hω U) hm
    rw [old_signed_actual_plus_proxy_eq M n r U.val U.property,
      old_signed_actual_minus_proxy_eq M n r U.val U.property] at hh
    rw [old_signed_actual_plus_proxy_eq M n r U.val U.property,
      old_signed_actual_minus_proxy_eq M n r U.val U.property]
    exact hh

end
end ASDExplicitGamma.Native
