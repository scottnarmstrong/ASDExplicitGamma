module

public import ASDExplicitGamma.Main.SourcePrefixGates
public import ASDExplicitGamma.Main.ErrorCoefficients

/-! Closed scalar concavity and support for the literal calibrated main envelopes. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Set

/-- The deterministic source upper bound for the OLD-frame shell clock. -/
noncomputable def mainSourceClock (gamma : ℝ) : ℝ := (443/125)*gamma*(3:ℝ)^(2*gamma)

theorem mainSourceClock_pos {gamma : ℝ} (hg : 0 < gamma) : 0 < mainSourceClock gamma := by
  unfold mainSourceClock
  positivity

end ASDExplicitGamma.Main
