module

public import ASDExplicitGamma.Inverse.RawShellBankCaps

/-! Degree bookkeeping for the OLD generic/refined source rows.  The full
response input below is the exact p=128 attenuated profile in IN-FULL-RESPONSE-BANK;
its eventual consumer can specialize this helper at the bank's law,
frame, cube, and attenuation parameters. -/
@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory
open scoped ENNReal

/-- The raw normalized-shell variance coefficient `e_h`. -/
noncomputable def nativeSourceRawShellVarianceCap (gamma : ℝ) (h : ℕ) : ℝ :=
  (9 / 2 : ℝ) * gamma * (3 : ℝ) ^ (2 * (h : ℝ) * gamma)

/-- The p=128 full-response coefficient `f_h`, using the exact outward
profile named in IN-FULL-RESPONSE-BANK. -/
noncomputable def nativeSourceFullResponseCap (gamma : ℝ) (h : ℕ) : ℝ :=
  Inverse.rawTraceFullResponseCap gamma h

end ASDExplicitGamma.Native
