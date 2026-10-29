module

public import ASDExplicitGamma.Native.ParentRowSourceMixedSpatial

/-! Literal parent source mixed terms dominated by their common-bank spatial envelope. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Triadic Algsuperdiff.Section3
noncomputable section

/-- The quadratic source term and both cross terms in the directional signed bill. -/
def parentRowSourceMixedCellBill (B A d E op om : ℝ) : ℝ :=
  B*d^2+2*(d*(Real.sqrt E+Real.sqrt ((B+1)^2*op^2+B*A*om^2)))

/-- Increasing the inverse and response histories preserves the full mixed bill. -/
theorem parent_row_source_mixed_cell_mono (B A C N d E op om : ℝ)
    (hB : 0≤B) (hA : 0≤A) (hBC : B≤C) (hAN : A≤N) (hd : 0≤d) :
    parentRowSourceMixedCellBill B A d E op om≤parentRowSourceMixedCellBill C N d E op om := by
  have hC : 0≤C := hB.trans hBC
  have hs := pow_le_pow_left₀ (add_nonneg hB (by norm_num : (0:ℝ)≤1))
    (add_le_add hBC le_rfl) 2
  have hm := mul_le_mul hBC hAN hA hC
  have hf := add_le_add (mul_le_mul_of_nonneg_right hs (sq_nonneg op))
    (mul_le_mul_of_nonneg_right hm (sq_nonneg om))
  exact add_le_add (mul_le_mul_of_nonneg_right hBC (sq_nonneg d))
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl (Real.sqrt_le_sqrt hf)) hd)
      (by norm_num : (0:ℝ)≤2))

/-- The actual cell histories and complete source size yield the common-bank source envelope.
The source norm, common inverse history and matrix majorant are proved on this same band. -/
theorem parent_row_actual_source_mixed_majorant
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ) (height : ℕ)
    (hpast : ∀ l<n,nativeInductionState M h l) (r : ℕ) (hr : r≤5)
    (t : ℝ) (ht : t≤1) (b : ℝ) (L : {l : ℝ // 0<l}) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      let Q := originCube 2 n
      let sigma : ℝ := Annealed.sigmaBar M n
      let hsigma := (Annealed.sigmaBar_characterization M n).1
      let k := pureFluxOpenResponseRestriction n (nativeSourceBandScalar n height t ω)
      let a := parentBoundaryBandFrameField M n height t ω
      let B := (nativeSourceBandHistory M n height t ω).toReal
      let W := parentBoundaryBandWeakProxy M n height r t ω
      let ka := parentBoundaryPotentialSourceClock Q r b L
      descendantsAverage Q r (fun U => parentRowSourceMixedCellBill
        (oldSignedInverseHistory U a) (oldSignedResponseHistory U a)
        (parentBoundaryCellSourceSize Q U M.nu sigma M.nu_pos hsigma k b L)
        (oldSignedFlatDirectionalMeanProxy Q U a b L true+oldSignedFlatDirectionalMeanProxy Q U a b L false)
        (oldSignedFlatOscillationSize Q U b L true) (oldSignedFlatOscillationSize Q U b L false))≤
      B*ka^2*W+2*(ka*Real.sqrt W*(Real.sqrt (parentBoundaryBandJointSpatialProxy M n height r t b L ω)+
        Real.sqrt (parentRowReciprocalSpatialEnergy M n height r t b L ω))) := by
  have hh := parent_row_cell_inverse_history M h hM hg n height hpast r hr t ht
  filter_upwards [hh] with ω hω
  dsimp only
  have hs := parent_row_source_mixed_spatial M n height r t ω b L
  rw [←old_signed_cell_average_eq_descendantsAverage]
  apply le_trans _ hs
  apply old_signed_cell_average_mono
  intro U
  apply parent_row_source_mixed_cell_mono
  · exact lemmaVInverseHistory_nonneg _ _ (Real.one_lt_rpow (by norm_num) (by norm_num))
  · exact ENNReal.toReal_nonneg
  · exact hω U.val U.property
  · exact (parent_boundary_band_matrix_history_bounds M n height r U.val U.property t ω).1
  · exact Real.sqrt_nonneg _

end
end ASDExplicitGamma.Native
