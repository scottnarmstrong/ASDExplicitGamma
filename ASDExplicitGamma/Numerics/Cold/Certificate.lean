module

public import ASDExplicitGamma.Numerics.Cold.RealDominance

/-! The exported cold recurrence certificate, combining its kernel replay and real meaning. -/

@[expose] public section

namespace ASDExplicitGamma.Numerics.Cold

/-- The complete cold numeric certificate: ROOT2, all 63 outward updates and positive
denominators, both endpoint values and the N2 D40 input bridge, and domination of every even
exact-real lag by its outward rational endpoint. -/
theorem cold_recurrence_certificate :
    coldL0 ^ 19 ≥ coldA ^ 9 * coldR20 ^ 10 ∧
    (∀ j ∈ coldUpdatedLags,
      0 < coldDenominator j ∧ coldMeanAt j = coldUpdate j) ∧
    coldMeanAt 40 = coldD40Target ∧
    coldMeanAt 128 = coldD128Target ∧
    coldMeanAt 40 ≤ (Spike.cold40Upper : ℚ) / 10^32 ∧
    coldMeanAt 128 < 1/200 ∧
    (∀ j ≤ 128, Even j → coldExactMean j ≤ (coldMeanAt j : ℝ)) := by
  refine ⟨coldRoot2, cold_lags_kernel_replay, coldD40_replay, coldD128_replay,
    coldD40_le_mainReturnInput_of_replay, coldD128_lt_oneTwoHundred_of_replay,
    cold_exact_mean_dominates⟩

end ASDExplicitGamma.Numerics.Cold
