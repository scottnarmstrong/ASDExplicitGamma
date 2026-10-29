module

public import ASDExplicitGamma.Native.HeatInitialNumericsDefsGen
public import ASDExplicitGamma.Native.HeatInitialRefinedNumeric

/-! The numeric certificates of the h-general refined initial moment, for `ns`
inserted shells.  Each field is the exact analogue of a fact the nine-shell row
used: the old-row cap of the per-shell variance factor, nonnegativity of the
moment list, and the outward root certificates.  They are proved for every
`9 ≤ ns ≤ 160` in `HeatInitialNumericsGen`. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native Algsuperdiff.Frozen.Assumptions

/-- Numeric certificates for the `ns`-shell refined initial moment. -/
structure NativeHeatGenNum (ns : ℕ) : Prop where
  efactor : ∀ γ : ℝ, 0 ≤ γ → γ ≤ gammaZero →
    (9 / 2 : ℝ) * γ * (3 : ℝ) ^ (2 * γ * (ns : ℝ)) ≤
      ((nativeHeatOldRowGen ns).e : ℝ)
  variance_nonneg : 0 ≤ nativeHeatGenVariance ns
  spectral_nonneg : 0 ≤ nativeHeatGenSpectral ns
  qm_nonneg : ∀ j : ℕ, j ≤ 20 → 0 ≤ (nativeHeatGenQm ns).getD j 0
  base : ∀ k : ℕ, 2 ≤ k → k ≤ 20 →
    nativeRootValid
      (nativeUp (((List.range (k + 1)).map fun j =>
        (Nat.choose k j : ℚ) *
          nativeInitialMeanMoment nativeHeatParametersData (k - j) *
          (2 * nativeHeatB) ^ j * (nativeHeatGenQm ns).getD j 0).sum)) k = true
  qroot : ∀ q : ℕ, 1 ≤ q → q ≤ 10 →
    nativeRootValid ((nativeHeatGenQm ns).getD q 0) q = true
  outer : ∀ q : ℕ, 1 ≤ q → q ≤ 10 →
    nativeRootValid (nativeRootUp ((nativeHeatGenQm ns).getD q 0) q) 2 = true

end ASDExplicitGamma.Native
