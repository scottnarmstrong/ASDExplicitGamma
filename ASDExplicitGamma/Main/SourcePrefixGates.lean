module

public import ASDExplicitGamma.Main.EnvelopeSigns
public import ASDExplicitGamma.Numerics.MainReturn.Observer01
public import Mathlib.Data.Rat.Cast.Order

/-! The exact source prefix constants clear the fixed main support point. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open ASDExplicitGamma.Numerics.MainReturn

/-- The literal initial mean input read once for all 40 source observers.
This is a numerical envelope input, not an asserted stochastic mean. -/
noncomputable def mainSourceMeanPrefix : ℝ := (observer1Panel0Data.initialMean : ℝ)

/-- The literal pre-reserve inverse input. The stored panel input already
includes 10^(-12), which is removed here before the envelope adds its reserve. -/
noncomputable def mainSourceInversePrefix : ℝ :=
  (observer1Panel0Data.initialInverseMean : ℝ)-(1/10^12)

theorem mainSourceMeanPrefix_gate : (1/100:ℝ) < mainSourceMeanPrefix := by
  change (1/100:ℝ) < (observer1Panel0Data.initialMean : ℝ)
  have h : (1/100:ℚ) < observer1Panel0Data.initialMean := by decide +kernel
  have hc := (Rat.cast_lt (K := ℝ)).2 h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_sub, Rat.cast_pow, Rat.cast_one] at hc
  exact hc

theorem mainSourceInversePrefix_gate : mainBetaOld/100 < mainSourceInversePrefix := by
  change (3683/2500/100:ℝ) < (observer1Panel0Data.initialInverseMean : ℝ)-(1/10^12)
  have h : (3683/2500/100:ℚ) < observer1Panel0Data.initialInverseMean-(1/10^12) := by decide +kernel
  have hc := (Rat.cast_lt (K := ℝ)).2 h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_sub, Rat.cast_pow, Rat.cast_one] at hc
  convert hc using 1 <;> norm_num

/-- Both source support gates now follow from the literal envelopes, with
no envelope-sign or panel-domain premise. -/
theorem mainSourceEnvelope_support_gates {v gamma theta t : ℝ}
    (hv : 0 ≤ v) (hg0 : 0 ≤ gamma) (hg : gamma ≤ gammaZero) (htheta : 0 ≤ theta) (ht : 0 ≤ t) :
    (1/100:ℝ) < mainEnvelopeA v gamma mainSourceMeanPrefix t ∧
      mainBetaOld/100 < mainEnvelopeXi v gamma mainSourceInversePrefix theta t :=
  mainEnvelope_support_gates hv hg0 hg htheta ht mainSourceMeanPrefix_gate mainSourceInversePrefix_gate

end ASDExplicitGamma.Main
