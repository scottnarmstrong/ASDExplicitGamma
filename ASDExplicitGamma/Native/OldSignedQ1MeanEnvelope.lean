module

public import ASDExplicitGamma.Native.OldSignedWeightedMeanTransport
public import ASDExplicitGamma.Numerics.Native.SetupQ1001Proof

/-! Certified first-moment fields of the unchanged OLD q1 panel. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Scalar Inverse Cold Variational Algsuperdiff.Section3
open Numerics Numerics.Native
noncomputable section

/-- The panel's depth-five first-moment envelope. -/
def oldSignedQ1PanelMean (t : ℝ) : ℝ :=
  nativeSetupQ1001FieldsR.getD 14 0+t*nativeSetupQ1001FieldsR.getD 11 0

/-- The panel's complete inverse-weighted weak-history envelope. -/
def oldSignedQ1PanelXi (t : ℝ) : ℝ :=
  nativeSetupQ1001FieldsR.getD 15 0+t*nativeSetupQ1001FieldsR.getD 12 0

/-- Rational slack for the initial means, transported slopes and rare reserve. -/
theorem old_signed_q1_mean_setup_lower :
    (7/50:ℝ)≤nativeSetupQ1001FieldsR.getD 14 0 ∧
    (1/50:ℝ)≤nativeSetupQ1001FieldsR.getD 11 0 ∧
    (231/1000:ℝ)≤nativeSetupQ1001FieldsR.getD 15 0 ∧
    (9/500:ℝ)≤nativeSetupQ1001FieldsR.getD 12 0 := by
  have h0q : (7/50:ℚ)≤(nativeSetupQ1001FieldsI.getD 14 nativeZeroInterval).lo := by decide +kernel
  have h1q : (1/50:ℚ)≤(nativeSetupQ1001FieldsI.getD 11 nativeZeroInterval).lo := by decide +kernel
  have h2q : (231/1000:ℚ)≤(nativeSetupQ1001FieldsI.getD 15 nativeZeroInterval).lo := by decide +kernel
  have h3q : (9/500:ℚ)≤(nativeSetupQ1001FieldsI.getD 12 nativeZeroInterval).lo := by decide +kernel
  refine ⟨le_trans ?_ (nativeSetupQ1001Fields_sound 14).1,
    le_trans ?_ (nativeSetupQ1001Fields_sound 11).1,
    le_trans ?_ (nativeSetupQ1001Fields_sound 15).1,
    le_trans ?_ (nativeSetupQ1001Fields_sound 12).1⟩
  · simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_one] using (Rat.cast_le (K := ℝ)).mpr h0q
  · simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_one] using (Rat.cast_le (K := ℝ)).mpr h1q
  · simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_one] using (Rat.cast_le (K := ℝ)).mpr h2q
  · simpa only [Rat.cast_div,Rat.cast_ofNat,Rat.cast_one] using (Rat.cast_le (K := ℝ)).mpr h3q

/-- The actual mean is below the exact panel field with its theta factor. -/
theorem old_signed_actual_q1_panel_mean
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ)
    (hpast : ∀ l≤n,nativeInductionState M h l) (t : ℝ) (ht : 0≤t ∧ t≤1) :
    inSourceMeanActual M n 5 t≤theta M*oldSignedQ1PanelMean t := by
  apply (old_signed_actual_mean_affine M h hM hg n hpast t ht).trans
  apply mul_le_mul_of_nonneg_left _ (cold_theta_pos M).le
  have hh := add_le_add old_signed_q1_mean_setup_lower.1
    (mul_le_mul_of_nonneg_left old_signed_q1_mean_setup_lower.2.1 ht.1)
  simpa only [oldSignedQ1PanelMean,mul_comm] using hh

/-- The unchanged weak-history field absorbs the entire rare reserve. -/
theorem old_signed_affine_le_q1_panel_xi (t : ℝ) (ht : 0≤t) :
    (23/100:ℝ)+(9/500)*t+1/10^12≤oldSignedQ1PanelXi t := by
  have hh := add_le_add old_signed_q1_mean_setup_lower.2.2.1
    (mul_le_mul_of_nonneg_left old_signed_q1_mean_setup_lower.2.2.2 ht)
  change _≤nativeSetupQ1001FieldsR.getD 15 0+t*nativeSetupQ1001FieldsR.getD 12 0
  linarith only [hh]

end
end ASDExplicitGamma.Native
