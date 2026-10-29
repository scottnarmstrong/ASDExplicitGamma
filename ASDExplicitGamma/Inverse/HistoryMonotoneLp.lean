module

public import ASDExplicitGamma.Inverse.HistoryPopulation

/-! Monotone convergence for nonnegative extended histories and infinite Minkowski. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory
open scoped ENNReal

/-- Monotone convergence and finite Minkowski bound the genuine extended series. -/
theorem history_ennreal_tsum_L20 {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) (f : ℕ → Ω → ℝ≥0∞) (hf : ∀ j, Measurable (f j)) :
    eLpNorm (fun ω => ∑' j, f j ω) 20 mu ≤ ∑' j, eLpNorm (f j) 20 mu := by
  let partialSum (N : ℕ) (ω : Ω) : ℝ≥0∞ := ∑ j ∈ Finset.range N, f j ω
  let S : ℝ≥0∞ := ∑' j, eLpNorm (f j) 20 mu
  have hpart (N : ℕ) : Measurable (partialSum N) :=
    Finset.measurable_sum _ (fun j _ => hf j)
  have hbound (N : ℕ) : eLpNorm (partialSum N) 20 mu ≤ S := by
    have he : (∑ j ∈ Finset.range N, f j) = partialSum N := by
      funext ω
      simp only [partialSum,Finset.sum_apply]
    have hb := eLpNorm_sum_le (μ := mu) (f := f) (s := Finset.range N) (by norm_num : (1:ℝ≥0∞) ≤ 20)
    rw [he] at hb
    exact hb.trans (ENNReal.sum_le_tsum (Finset.range N))
  have hpow (N : ℕ) : (∫⁻ ω, (partialSum N ω)^20 ∂mu) ≤ S^20 := by
    rw [← history_L20_power mu (partialSum N) (hpart N)]
    exact pow_le_pow_left' (hbound N) 20
  have hmono : Monotone (fun N ω => (partialSum N ω)^20) := by
    intro N K hNK ω
    apply pow_le_pow_left' _ 20
    exact Finset.sum_le_sum_of_subset (Finset.range_mono hNK)
  have hmoment : (eLpNorm (fun ω => ∑' j, f j ω) 20 mu)^20 ≤ S^20 := by
    rw [history_L20_power mu _ (Measurable.tsum hf)]
    calc
      _ = ∫⁻ ω, ⨆ N, (partialSum N ω)^20 ∂mu := by
        apply lintegral_congr_ae
        exact Filter.Eventually.of_forall (fun ω => by
          dsimp only
          rw [ENNReal.tsum_eq_iSup_nat,ENNReal.iSup_pow])
      _ = ⨆ N, ∫⁻ ω, (partialSum N ω)^20 ∂mu := lintegral_iSup (fun N => (hpart N).pow_const 20) hmono
      _ ≤ S^20 := iSup_le hpow
  apply (ENNReal.rpow_le_rpow_iff (by norm_num : (0:ℝ) < 20)).mp
  simpa only [show (20 : ℝ) = ((20 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast] using hmoment

end ASDExplicitGamma.Inverse
