module

public import ASDExplicitGamma.Native.HeatIndividualOldCertificates
public import ASDExplicitGamma.Native.GenericSourceActualProfile

/-! Endpoint variance and full-response profiles in the exact OLD slots. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native
noncomputable section

/-- The OLD variance slot is exactly the finite rational endpoint clock. -/
theorem heat_old_variance_endpoint (height : ℕ) :
    ((nativeOld height).e:ℝ) = nativeSourceGenericVarianceCap (17/50000) height := by
  change (((9/2)*nativeGamma*nativeE (2*nativeGamma*height):ℚ):ℝ) = _
  simp only [nativeSourceGenericVarianceCap,nativeSourceE,nativeE,nativeGamma,
    Rat.cast_mul,Rat.cast_div,Rat.cast_sub,Rat.cast_ofNat,Rat.cast_natCast]
  ring

/-- Outward rounding in the OLD full-response slot is preserved. -/
theorem heat_old_full_endpoint (height : ℕ) :
    nativeSourceGenericFullResponseCap (17/50000) height ≤ ((nativeOld height).f:ℝ) := by
  let f : ℚ := 4*((1009309/500000)+nativeGamma*(32474*(height+1)+11483216))*
    nativeE ((2*height+4)*nativeGamma)
  have h : (f:ℝ) ≤ (nativeUp f:ℝ) := by exact_mod_cast nativeUp_ge f
  change _ ≤ (nativeUp f:ℝ)
  apply le_trans (le_of_eq ?_) h
  dsimp [f,nativeSourceGenericFullResponseCap,nativeSourceE,nativeE,nativeGamma]
  push_cast
  ring

/-- Both actual unrounded source profiles fit their OLD slots on the finite
prefix. This comparison is independent of the cooperative moment output. -/
theorem heat_source_profiles_le_old (gamma : ℝ) (height : ℕ)
    (hg0 : 0 ≤ gamma) (hg : gamma ≤ 17/50000) (hh : height ≤ 1332) :
    nativeSourceRawShellVarianceCap gamma height ≤ ((nativeOld height).e:ℝ) ∧
    nativeSourceFullResponseCap gamma height ≤ ((nativeOld height).f:ℝ) := by
  have htheta : gamma/(17/50000:ℝ) ≤ 1 := (div_le_one₀ (by norm_num)).2 hg
  have he0 : 0 ≤ nativeSourceGenericVarianceCap (17/50000) height := by
    have hE := native_source_E_nonneg (17/50000) height (by norm_num) (by norm_num) (by omega)
    unfold nativeSourceGenericVarianceCap
    positivity
  constructor
  · rw [heat_old_variance_endpoint]
    apply (native_source_true_variance_le_generic gamma height hg0 hg (by omega)).trans
    have he := native_source_generic_variance_cap_degree gamma (gamma/(17/50000)) height
      hg0 hg rfl (by omega)
    exact he.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right htheta he0)
  · exact (native_source_generic_full_response_cap_le_bank gamma height hg0 hg hh).trans
      ((native_source_generic_full_response_cap_degree gamma height hg0 hg hh).trans
        (heat_old_full_endpoint height))

end
end ASDExplicitGamma.Native
