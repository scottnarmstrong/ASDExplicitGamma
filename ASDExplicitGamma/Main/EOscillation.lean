module

public import ASDExplicitGamma.Main.ErrorCoefficients

/-! Exact source form of the MA-E-OSCILLATION scalar contribution. -/

@[expose] public section

namespace ASDExplicitGamma.Main

noncomputable section

/-- The source oscillation contribution `2 d q` in the specified OLD frame. -/
def mainEOscillationSourceProfile
    (d H op om : ℝ) : ℝ := 2 * d * mainLoadQ H op om

end

end ASDExplicitGamma.Main
