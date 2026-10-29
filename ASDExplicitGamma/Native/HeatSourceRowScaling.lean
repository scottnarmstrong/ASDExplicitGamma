module

public import ASDExplicitGamma.Numerics.Native.State

/-! Exact source-row normalization, retaining the augmented forcing column. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Numerics.Native

/-- The positive-degree diagonal is the unscaled source diagonal. -/
theorem native_scaled_source_diagonal (coeff : NativeSystemCoefficients) (rr z : ℚ)
    (k : ℕ) :
    (nativeScaledFrom coeff rr z).diag.getD (k+1) 0 = coeff.beta.getD k 0 := by
  simp [nativeScaledFrom]

/-- Undoing the positive source scale restores the predecessor coefficient. -/
theorem native_scaled_source_subdiagonal (coeff : NativeSystemCoefficients) (rr z : ℚ)
    (hz : z ≠ 0) (k : ℕ) :
    (nativeScaledFrom coeff rr z).subdiag.getD (k+1) 0*z = coeff.alpha.getD k 0 := by
  cases he : coeff.alpha[k]? <;> simp [nativeScaledFrom,he,hz]

/-- Undoing the degree-dependent scale restores the entire forcing; no part
of the remainder is dropped into the fixed zeroth coordinate. -/
theorem native_scaled_source_forcing (coeff : NativeSystemCoefficients) (rr z : ℚ)
    (hz : z ≠ 0) (k : ℕ) (hk : k < 20) :
    (nativeScaledFrom coeff rr z).force.getD (k+1) 0*z^(k+1) = coeff.force.getD k 0 := by
  simp [nativeScaledFrom,hk,hz]

/-- Degree indexing of the exact individual source producer. -/
theorem native_individual_coefficients_row (h k : ℕ) (old : NativeOldRow) (hk : k < 20) :
    (nativeIndividualCoefficients h old).alpha.getD k 0 = (nativeIndividualRow h (k+1) old).1 ∧
    (nativeIndividualCoefficients h old).beta.getD k 0 = (nativeIndividualRow h (k+1) old).2.1 ∧
    (nativeIndividualCoefficients h old).force.getD k 0 = (nativeIndividualRow h (k+1) old).2.2 := by
  simp [nativeIndividualCoefficients,hk]

/-- All three source coefficients are recovered together; this is an exact
identity, including rounding in the source producer, not an error comparison. -/
theorem native_individual_scaled_source_row (h k : ℕ) (old : NativeOldRow)
    (rr z : ℚ) (hz : z ≠ 0) (hk : k < 20) :
    let s := nativeScaledFrom (nativeIndividualCoefficients h old) rr z
    let c := nativeIndividualRow h (k+1) old
    s.diag.getD (k+1) 0 = c.2.1 ∧
    s.subdiag.getD (k+1) 0*z = c.1 ∧
    s.force.getD (k+1) 0*z^(k+1) = c.2.2 := by
  have hc := native_individual_coefficients_row h k old hk
  exact ⟨(native_scaled_source_diagonal _ rr z k).trans hc.2.1,
    (native_scaled_source_subdiagonal _ rr z hz k).trans hc.1,
    (native_scaled_source_forcing _ rr z hz k hk).trans hc.2.2⟩

end ASDExplicitGamma.Native
