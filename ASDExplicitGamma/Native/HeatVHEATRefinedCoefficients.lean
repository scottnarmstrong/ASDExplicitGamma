module

public import ASDExplicitGamma.Inverse.SourceChildCovarianceBudget
public import ASDExplicitGamma.Numerics.Native.Heat

/-! Exact coefficient budgets for the nine refined physical shells. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Inverse
open ASDExplicitGamma.Numerics.Native
open ASDExplicitGamma.Variational

/-- The finite nine-shell deterministic drift and covariance-remainder
coefficients are bounded by the configured refined `K` and `M` budgets. -/
theorem nativeHeatQ3RefinedShellCoefficientSums_le :
    (∑ d : Fin 9,
      lemmaVH2kn (pureFluxCovarianceRho 1 d.val)
        (pureFluxCovarianceDelta 1 d.val)) ≤ (nativeHeatK : ℝ) ∧
    (∑ d : Fin 9,
      pureFluxCovarianceMu (pureFluxCovarianceA 1 d.val)
        (pureFluxCovarianceB 1 d.val)) ≤ (nativeHeatM : ℝ) := by
  have hsum := source_child_covariance_weighted_partial_sums
    (Finset.range 9) (fun _ : ℕ => 1) 1 (by norm_num)
    (by intro i hi; norm_num)
  have hk :
      (∑ d : Fin 9,
        lemmaVH2kn (pureFluxCovarianceRho 1 d.val)
          (pureFluxCovarianceDelta 1 d.val)) =
        ∑ i ∈ Finset.range 9,
          lemmaVH2kn (pureFluxCovarianceRho 1 i)
            (pureFluxCovarianceDelta 1 i) :=
    Fin.sum_univ_eq_sum_range
      (fun i : ℕ => lemmaVH2kn (pureFluxCovarianceRho 1 i)
        (pureFluxCovarianceDelta 1 i)) 9
  have hm :
      (∑ d : Fin 9,
        pureFluxCovarianceMu (pureFluxCovarianceA 1 d.val)
          (pureFluxCovarianceB 1 d.val)) =
        ∑ i ∈ Finset.range 9,
          pureFluxCovarianceMu (pureFluxCovarianceA 1 i)
            (pureFluxCovarianceB 1 i) :=
    Fin.sum_univ_eq_sum_range
      (fun i : ℕ => pureFluxCovarianceMu (pureFluxCovarianceA 1 i)
        (pureFluxCovarianceB 1 i)) 9
  constructor
  · calc
      _ = ∑ i ∈ Finset.range 9,
          lemmaVH2kn (pureFluxCovarianceRho 1 i)
            (pureFluxCovarianceDelta 1 i) := hk
      _ ≤ (65399707 / 10^9 : ℝ) := by simpa only [one_mul, mul_one] using hsum.1
      _ = (nativeHeatK : ℝ) := by norm_num [nativeHeatK]
  · calc
      _ = ∑ i ∈ Finset.range 9,
          pureFluxCovarianceMu (pureFluxCovarianceA 1 i)
            (pureFluxCovarianceB 1 i) := hm
      _ ≤ (259713047 / 10^9 : ℝ) := by simpa only [one_mul, mul_one] using hsum.2
      _ = (nativeHeatM : ℝ) := by norm_num [nativeHeatM]

end ASDExplicitGamma.Native
