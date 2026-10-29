module

public import ASDExplicitGamma.Cold.ColdTableConstants

/-! # Sign and root bounds for the entire deterministic cap functions -/

@[expose] public section
namespace ASDExplicitGamma.Cold
open ASDExplicitGamma.Numerics.Cold

/-- Every stored moment entry is bounded by the native root cap. -/
theorem cold_moment_table_root_bound : ∀ k ∈ List.range 129, coldMomentAt k ≤ coldR20 := by
  decide +kernel

/-- Outside its finite stored domain each cap function is exactly its declared zero fallback. -/
theorem cold_table_fallback {k : ℕ} (hk : 129 ≤ k) : coldMomentAt k = 0 ∧ coldMeanAt k = 0 := by
  have hsM : coldMomentData.size = 129 := rfl
  have hsD : coldMeanData.size = 129 := rfl
  have hnM : ¬k < coldMomentData.size := by omega
  have hnD : ¬k < coldMeanData.size := by omega
  constructor
  · simp only [coldMomentAt,Array.getD,dite_eq_right hnM]
  · simp only [coldMeanAt,Array.getD,dite_eq_right hnD]

/-- All deterministic moment/mean cap functions have the global signs used by the history API.
The zero fallback is part of the existing table definition, not an estimate at uncomputed lags. -/
theorem cold_table_global_bounds (k : ℕ) : 0 ≤ coldMomentAt k ∧ coldMomentAt k ≤ coldR20 ∧ 0 ≤ coldMeanAt k := by
  by_cases hk : k < 129
  · have hn := cold_table_nonneg k (List.mem_range.mpr hk)
    exact ⟨hn.2,cold_moment_table_root_bound k (List.mem_range.mpr hk),hn.1⟩
  · have he := cold_table_fallback (by omega : 129 ≤ k)
    rw [he.1,he.2]
    norm_num [coldR20]

end ASDExplicitGamma.Cold
