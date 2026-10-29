module

public import ASDExplicitGamma.Native.HeatStepDefs

/-! Numerical certificates for the configured refined-child heat frames at `ns` shells:
every outward root appearing in `nativeHeatFrames` and in the sharp frame shift is a checked
root, and the 20th root `Q_N` of the 20th Gaussian clock moment is a checked outward root. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native

/-- The radicand of the shifted-frame argument at `ns` shells: `t₀ = min(old.x, individual)`. -/
def nativeHeatShiftArgGen (ns : ℕ) : ℚ :=
  min (nativeHeatOldRowGen ns).x (nativeHeatIndividualGen ns).1

/-- Root certificates of the frames. -/
structure NativeHeatStepFrameNum (ns : ℕ) : Prop where
  qN_root : nativeRootValid ((nativeHeatGenQm ns).getD 20 0) 20 = true
  shift_root : nativeRootValid
    (nativeHeatShiftArgGen ns * (nativeHeatShiftArgGen ns + 8)) 2 = true
  y0_root : nativeRootValid (nativeHeatY0Gen ns) 2 = true
  xp_root : nativeRootValid
    (2 * nativeHeatB * nativeHeatParametersData.gm.getD 20 0 * nativeHeatGenVariance ns) 2 = true
  yp_root : nativeRootValid
    (2 * nativeHeatB * nativeHeatQNGen ns +
      2 * nativeHeatEps * nativeHeatParametersData.gm.getD 20 0 * nativeHeatGenVariance ns) 2 = true
  f_root : nativeRootValid (nativeHeatRQ * (nativeHeatOldRowGen ns).f) 2 = true
  fr_root : nativeRootValid (2 * nativeHeatB * 255 * nativeHeatGenVariance ns) 2 = true

end ASDExplicitGamma.Native

end
