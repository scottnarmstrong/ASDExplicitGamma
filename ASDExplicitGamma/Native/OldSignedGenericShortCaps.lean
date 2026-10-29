module

public import ASDExplicitGamma.Native.OldSignedInitialGenericMean

/-! Coarse rational gates for the generic initial-law producer at short depths. -/
@[expose] public section
namespace ASDExplicitGamma.Native
noncomputable section

/-- The rational frame factor on the short initial-law prefix. -/
theorem old_signed_generic_E_short (h : ℕ) (hh : h≤72) :
    0≤nativeSourceE (17/50000) h ∧ nativeSourceE (17/50000) h≤53/50 := by
  have hhR : (h:ℝ)≤72 := by exact_mod_cast hh
  have hden : 0<1-(11/10:ℝ)*(2*(h:ℝ)*(17/50000)) := by linarith only [hhR]
  constructor
  · exact inv_nonneg.mpr hden.le
  · unfold nativeSourceE
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hden).mpr
    linarith only [hhR]

/-- Crude variance and full-response caps are sufficient here because the
individual L20 input appears only multiplied by the tiny rare reserve. -/
theorem old_signed_generic_short_variance_full (h : ℕ) (hh : h≤70) :
    0≤nativeSourceGenericVarianceCap (17/50000) h ∧
    nativeSourceGenericVarianceCap (17/50000) h≤17/10000 ∧
    0≤nativeSourceGenericFullResponseCap (17/50000) h ∧
    nativeSourceGenericFullResponseCap (17/50000) h≤100000 := by
  have he := old_signed_generic_E_short h (by omega)
  have hf := old_signed_generic_E_short (h+2) (by omega)
  have hhR : (h:ℝ)≤70 := by exact_mod_cast hh
  have hpoly : 0≤(1009309:ℝ)/500000+(17/50000)*
      (32474*((h+1:ℕ):ℝ)+11483216) := by positivity
  have hpolycap : (1009309:ℝ)/500000+(17/50000)*
      (32474*((h+1:ℕ):ℝ)+11483216)≤5000 := by
    push_cast
    linarith only [hhR]
  refine ⟨mul_nonneg (by norm_num) he.1, ?_,
    mul_nonneg (mul_nonneg (by norm_num) hpoly) hf.1, ?_⟩
  · unfold nativeSourceGenericVarianceCap
    have hx := mul_le_mul_of_nonneg_left he.2 (by norm_num : (0:ℝ)≤(9/2)*(17/50000))
    linarith only [hx]
  · unfold nativeSourceGenericFullResponseCap
    have hx := mul_le_mul (mul_le_mul_of_nonneg_left hpolycap (by norm_num : (0:ℝ)≤4))
      hf.2 hf.1 (by norm_num : (0:ℝ)≤4*5000)
    exact hx.trans (by norm_num)

/-- Every refinement is bounded by the unrefined generic producer. -/
theorem old_signed_generic_pass_le_raw (h : ℕ) (a e f : ℝ) (k : ℕ) :
    nativeSourceGenericPassCap h a e f k ≤ nativeSourceRawMomentIncrement h e f := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact (min_le_left _ _).trans ih

private theorem generic_raw_short_scalar (h e f : ℝ)
    (hh : h≤70) (he0 : 0≤e) (he : e≤17/10000) (hf0 : 0≤f) (hf : f≤100000) :
    e*((78*h+76*(521/1000))*(3683/2500)+
      2*(521/1000)*(3683/2500)*f+
      ((1975/1000)+38*(1565/1000))*(3683/2500)^2*f)≤100000 := by
  have heh := mul_le_mul_of_nonneg_left hh he0
  have hef := mul_le_mul he hf hf0 (by norm_num : (0:ℝ)≤17/10000)
  nlinarith only [heh,hef,he]

/-- A deliberately loose L20 gate is enough to pay all generic rare terms. -/
theorem old_signed_generic_individual_short (h : ℕ) (hh : h≤70) :
    0≤nativeSourceGenericIndividualProfile (17/50000) 1 h ∧
    nativeSourceGenericIndividualProfile (17/50000) 1 h≤1000000 := by
  have hc := old_signed_generic_short_variance_full h hh
  have hpass := old_signed_generic_pass_le_raw h ((3/50:ℝ)*1)
    (nativeSourceGenericVarianceCap (17/50000) h)
    (nativeSourceGenericFullResponseCap (17/50000) h) 4
  have hraw := generic_raw_short_scalar (h:ℝ) _ _ (by exact_mod_cast hh)
    hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  have hraw' : nativeSourceRawMomentIncrement h (nativeSourceGenericVarianceCap (17/50000) h)
      (nativeSourceGenericFullResponseCap (17/50000) h)≤100000 := by
    simpa only [nativeSourceRawMomentIncrement,nativeSourceK,nativeSourceB128,nativeSourceM,
      nativeSourceQ] using hraw
  refine ⟨native_source_generic_individual_profile_nonneg _ _ h (by norm_num) (by norm_num)
    le_rfl (by omega),?_⟩
  unfold nativeSourceGenericIndividualProfile nativeSourceGenericIndividualCap
  linarith only [hpass,hraw']

end
end ASDExplicitGamma.Native
