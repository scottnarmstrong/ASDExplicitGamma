module

public import ASDExplicitGamma.Native.OldSignedInitialHistory

/-! Exact population and complete-series payment for the OLD maximum history. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Cold Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- The source population loss changes alpha exactly to beta. -/
theorem old_signed_max_history_population_weight (j : ℕ) :
    ENNReal.ofReal (inverseHistoryDiscount^j)*((9:ℝ≥0∞)^j)^(1/20:ℝ)=
      ENNReal.ofReal (coldHistoryBeta^j) := by
  rw [cold_native_beta_power]
  have ha : inverseHistoryDiscount^j=(3:ℝ)^(-(1/4:ℝ)*(j:ℝ)) := by
    unfold inverseHistoryDiscount
    rw [←Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤3)]
  rw [ha]
  exact history_population_weight j

/-- A finite actual L20 history cap lowers to the real L2 carrier used by
the matrix and corrector bills. The history identity supplies finiteness. -/
theorem old_signed_actual_max_history_L2_of_L20
    (M : ABKModel 2) (n : ℤ) (r : ℕ) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth (originCube 2 n) r) (t C : ℝ) (hC : 0 ≤ C)
    (hcap : eLpNorm (Main.mainOrdinaryTraceMaxHistory M n U t)
      20 (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal C) :
    MemLp (fun ω => oldSignedMaxTraceHistory U (oldSignedPartialFrameField M n 1 t ω))
      2 (Cutoff.cutoffSampleLaw M).toMeasure ∧
    lpNorm (fun ω => oldSignedMaxTraceHistory U (oldSignedPartialFrameField M n 1 t ω))
      2 (Cutoff.cutoffSampleLaw M).toMeasure ≤ C := by
  let H := fun ω => oldSignedMaxTraceHistory U (oldSignedPartialFrameField M n 1 t ω)
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  have hn : ∀ ω,0≤H ω := old_signed_actual_max_trace_history_nonneg M n r U hU t
  have he : eLpNorm H 2 μ=eLpNorm (Main.mainOrdinaryTraceMaxHistory M n U t) 2 μ := by
    rw [show Main.mainOrdinaryTraceMaxHistory M n U t = fun ω => ENNReal.ofReal (H ω) from
      funext (old_signed_actual_max_trace_history M n r U hU t)]
    exact (eLpNorm_ofReal H (Filter.Eventually.of_forall hn)).symm
  have hh : eLpNorm H 2 μ ≤ ENNReal.ofReal C := by
    rw [he]
    exact (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (2:ℝ≥0∞)≤20)).trans hcap
  refine ⟨?_,?_⟩
  · rw [memLp_iff]
    exact lt_of_le_of_lt hh ENNReal.ofReal_lt_top
  · exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hh).trans_eq (ENNReal.toReal_ofReal hC)

end
end ASDExplicitGamma.Native
