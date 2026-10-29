module

public import ASDExplicitGamma.Cold.ColdMomentTable
public import ASDExplicitGamma.Cold.Interpolation
public import ASDExplicitGamma.Cold.ColdRoundingAlgebra

/-! # Analytic consumption of the nineteenth-power interpolation certificates -/

@[expose] public section
noncomputable section
open MeasureTheory
namespace ASDExplicitGamma.Cold
open ASDExplicitGamma.Numerics.Cold

/-- The graph/interpolation endpoints used by the replay are nonnegative. -/
theorem cold_graph_table_nonneg : ∀ k ∈ List.range 127,
    0 ≤ coldInterpolationAt k ∧ 0 ≤ coldVUpper k ∧ 0 ≤ coldGraphRootAt k ∧
      0 ≤ coldGraphAt k := by
  decide +kernel

/-- The finite choice table always selects an available earlier-or-equal cell lag. -/
theorem cold_graph_choice_lag : ∀ ell ∈ List.range 127,
    (coldGraphChoiceAt ell-1)/2 ≤ ell ∧ (coldGraphChoiceAt ell-2)/2 ≤ ell := by
  decide +kernel

/-- Exact variance radicals fit the stored outward root endpoints. -/
theorem cold_variance_radical_table {k : ℕ} (hk : k ≤ 126) :
    Real.sqrt (2*(coldMeanAt k:ℝ)+(coldInterpolationAt k:ℝ)^2) ≤ (coldVUpper k:ℝ) := by
  have hkmem : k ∈ List.range 127 := List.mem_range.mpr (by omega)
  have hp : (2*(coldMeanAt k:ℝ)+(coldInterpolationAt k:ℝ)^2) ≤ (coldVUpper k:ℝ)^2 := by
    have hround := cold_round_up_real (2*coldMeanAt k+coldInterpolationAt k^2)
    have hs : (coldRoundUp (2*coldMeanAt k+coldInterpolationAt k^2):ℝ) ≤ (coldVUpper k:ℝ)^2 := by
      exact_mod_cast (cold_v_endpoints_check k hkmem).1
    simpa only [Rat.cast_add,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_pow] using hround.trans hs
  exact (Real.sqrt_le_iff).mpr ⟨Rat.cast_nonneg.mpr (cold_graph_table_nonneg k hkmem).2.1,hp⟩

end ASDExplicitGamma.Cold
