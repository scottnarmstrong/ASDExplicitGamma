module

public import ASDExplicitGamma.Native.VanishingBracket
public import ASDExplicitGamma.Triadic.PlanarDirectionVolume
public import ASDExplicitGamma.Numerics.Native.Heat

/-! Exact decomposition of the configured heat forcing into its fixed rare
remainder and the OLD-bank-weighted quadratic bracket contribution. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native

/-- The fixed terms in the VHEAT error row: both inverse-reserve orders and
the mixed OLD remainder terms are kept with their source coefficients. -/
def nativeHeatFixedAnalyticRemainder
    (old : NativeOldRow) (frames : NativeHeatFrameInputs) (k : ℕ) : ℚ :=
  let j1prev := nativeHeatRareJ frames 1 (k - 1)
  let j1 := nativeHeatRareJ frames 1 k
  let j2prev := nativeHeatRareJ frames 2 (k - 1)
  let j2 := nativeHeatRareJ frames 2 k
  let base := (k : ℚ) * old.e *
    ((2 * nativeHeatK + 2 * nativeHeatB * nativeHeatM) *
        (4 * j1prev + j1) +
      nativeHeatM * (4 * j2prev + j2))
  if k ≥ 2 then
    base + 2 * (k : ℚ) * ((k : ℚ) - 1) * old.e * nativeHeatSB *
      (1 + 1 / nativeHeatTheta) *
      (2 * nativeHeatB * (4 * j1prev + j1) + 4 * j2prev + j2)
  else
    base

/-- The heat-augmented OLD-bank bracket remainder in the producer's exact
coefficient form. It is zero in degree one, as required by VHEAT. -/
def nativeHeatBracketRemainderAt
    (old : NativeOldRow) (frames : NativeHeatFrameInputs) (y : ℚ) (k : ℕ) : ℚ :=
  if k ≥ 2 then
    2 * (k : ℚ) * ((k : ℚ) - 1) * old.e * nativeHeatSB *
      (1 + 1 / nativeHeatTheta) * nativeHeatB ^ 2 * y ^ (k - 2) *
        (4 * frames.x + frames.x ^ 2)
  else
    0

/-- The configured numerical error row is exactly the complete fixed VHEAT
remainder, including both OLD-bank rare orders and the retained mixed term. -/
theorem nativeHeatFixedAt_eq_explicit_remainder
    (old : NativeOldRow) (frames : NativeHeatFrameInputs) (k : ℕ) :
    nativeHeatFixedAt old frames k =
      nativeUp (nativeHeatFixedAnalyticRemainder old frames k) := by
  simp [nativeHeatFixedAt, nativeHeatFixedAnalyticRemainder]

/-- Each augmented forcing step adds the full quadratic bracket term to the
fixed VHEAT remainder before outward rounding; no degree-two-or-higher term is
discarded. -/
theorem nativeHeatForcingAt_eq_explicit_remainder
    (old : NativeOldRow) (frames : NativeHeatFrameInputs)
    (fixed : List ℚ) (y : ℚ) (k : ℕ) :
    nativeHeatForcingAt old frames fixed y k =
      nativeUp (fixed.getD (k - 1) 0 +
        nativeHeatBracketRemainderAt old frames y k) := by
  by_cases hk : 2 ≤ k
  · simp [nativeHeatForcingAt, nativeHeatBracketRemainderAt, hk]
  · simp [nativeHeatForcingAt, nativeHeatBracketRemainderAt, hk]

/-- The explicit heat bracket remainder is nonnegative for nonnegative OLD
energy, heat-trace envelope, and averaged envelope. -/
theorem nativeHeatBracketRemainderAt_nonneg
    (old : NativeOldRow) (frames : NativeHeatFrameInputs) (y : ℚ) (k : ℕ)
    (hold : 0 ≤ old.e) (hx : 0 ≤ frames.x) (hy : 0 ≤ y) :
    0 ≤ nativeHeatBracketRemainderAt old frames y k := by
  by_cases hk : 2 ≤ k
  · have hSB : 0 ≤ nativeHeatSB := by norm_num [nativeHeatSB]
    have hθ : 0 < nativeHeatTheta := by norm_num [nativeHeatTheta]
    have hkq : (1 : ℚ) ≤ (k : ℚ) := by
      exact_mod_cast (show 1 ≤ k by omega)
    have hkm1 : 0 ≤ (k : ℚ) - 1 := by linarith
    simp only [nativeHeatBracketRemainderAt, hk]
    positivity
  · simp [nativeHeatBracketRemainderAt, hk]

end ASDExplicitGamma.Native
