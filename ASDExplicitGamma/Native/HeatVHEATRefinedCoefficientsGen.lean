module

public import ASDExplicitGamma.Native.HeatVHEATRefinedCoefficients
public import ASDExplicitGamma.Native.HeatVHEATSourceCarrierGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedShellLawGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceClocksGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedSourceProfilesGen
public import ASDExplicitGamma.Native.HeatVHEATRefinedSourceTransportGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceGeometryGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceBankGen
public import ASDExplicitGamma.Native.HeatVHEATDriftBankIdentityGen
public import ASDExplicitGamma.Native.HeatVHEATDriftBankMeasurableGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceIntegrandGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceNormsGen
public import ASDExplicitGamma.Native.HeatVHEATDriftSourceExpectationGen

/-! The `ns`-shell generalization of `HeatVHEATRefinedCoefficients`. -/

@[expose] public section


namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Inverse
open ASDExplicitGamma.Numerics.Native
open ASDExplicitGamma.Variational

variable (ns : ℕ)

/-- The finite nine-shell deterministic drift and covariance-remainder
coefficients are bounded by the configured refined `K` and `M` budgets. -/
theorem nativeHeatQ3RefinedShellCoefficientSums_le_Gen :
    (∑ d : Fin ns,
      lemmaVH2kn (pureFluxCovarianceRho 1 d.val)
        (pureFluxCovarianceDelta 1 d.val)) ≤ (nativeHeatK : ℝ) ∧
    (∑ d : Fin ns,
      pureFluxCovarianceMu (pureFluxCovarianceA 1 d.val)
        (pureFluxCovarianceB 1 d.val)) ≤ (nativeHeatM : ℝ) := by
  have hsum := source_child_covariance_weighted_partial_sums
    (Finset.range ns) (fun _ : ℕ => 1) 1 (by norm_num)
    (by intro i hi; norm_num)
  have hk :
      (∑ d : Fin ns,
        lemmaVH2kn (pureFluxCovarianceRho 1 d.val)
          (pureFluxCovarianceDelta 1 d.val)) =
        ∑ i ∈ Finset.range ns,
          lemmaVH2kn (pureFluxCovarianceRho 1 i)
            (pureFluxCovarianceDelta 1 i) :=
    Fin.sum_univ_eq_sum_range
      (fun i : ℕ => lemmaVH2kn (pureFluxCovarianceRho 1 i)
        (pureFluxCovarianceDelta 1 i)) ns
  have hm :
      (∑ d : Fin ns,
        pureFluxCovarianceMu (pureFluxCovarianceA 1 d.val)
          (pureFluxCovarianceB 1 d.val)) =
        ∑ i ∈ Finset.range ns,
          pureFluxCovarianceMu (pureFluxCovarianceA 1 i)
            (pureFluxCovarianceB 1 i) :=
    Fin.sum_univ_eq_sum_range
      (fun i : ℕ => pureFluxCovarianceMu (pureFluxCovarianceA 1 i)
        (pureFluxCovarianceB 1 i)) ns
  constructor
  · calc
      _ = ∑ i ∈ Finset.range ns,
          lemmaVH2kn (pureFluxCovarianceRho 1 i)
            (pureFluxCovarianceDelta 1 i) := hk
      _ ≤ (65399707 / 10^9 : ℝ) := by simpa only [one_mul, mul_one] using hsum.1
      _ = (nativeHeatK : ℝ) := by norm_num [nativeHeatK]
  · calc
      _ = ∑ i ∈ Finset.range ns,
          pureFluxCovarianceMu (pureFluxCovarianceA 1 i)
            (pureFluxCovarianceB 1 i) := hm
      _ ≤ (259713047 / 10^9 : ℝ) := by simpa only [one_mul, mul_one] using hsum.2
      _ = (nativeHeatM : ℝ) := by norm_num [nativeHeatM]

end ASDExplicitGamma.Native
