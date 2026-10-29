module

public import ASDExplicitGamma.Scalar.UpperCellEnergyFutureWeightedTerm

/-! The complete random full-response history, with a proved finite norm
budget and explicit almost-sure finiteness before any toReal interpretation. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Algsuperdiff.Section3 Native Inverse
open scoped ENNReal
noncomputable section

def upperCellFutureHistory (M : ABKModel 2) (n : ℤ) (height : ℕ)
    (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) : ℝ≥0∞ :=
  ∑' j : ℕ, ENNReal.ofReal (upperCellHistoryWeight j)*
    upperCellFutureDepthMax M n height j weights ω

/-- The complete full-response history has a finite order-64 budget. The
export explicitly rules out an infinite history on almost every sample. -/
theorem upper_cell_future_history_L64
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ)
    (hpast : ∀ k < n, nativeInductionState M h k)
    (height : ℕ) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc n (n+(height:ℤ)), 0 ≤ weights k ∧ weights k ≤ 1) :
    eLpNorm (fun ω => (upperCellFutureHistory M n height weights ω).toReal) 64
      (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (4*∑' j : ℕ, nativeFullResponse64FutureTerm M.gamma ((height:ℝ)+15) 15 j) ∧
    (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      upperCellFutureHistory M n height weights ω < ⊤) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let f := fun j ω => upperCellHistoryWeight j*
    (upperCellFutureDepthMax M n height j weights ω).toReal
  let b := fun j => 4*nativeFullResponse64FutureTerm M.gamma ((height:ℝ)+15) 15 j
  have hf (j) : Measurable (f j) :=
    (upper_cell_future_depth_max_measurable M n height j weights).ennreal_toReal.const_mul _
  have hf0 (j) (ω : Cutoff.CutoffSample 2) : 0 ≤ f j ω :=
    mul_nonneg (upper_cell_history_weight_nonneg j) ENNReal.toReal_nonneg
  have ha : 0 ≤ 1-(3:ℝ)^(-(1/4:ℝ)) := sub_nonneg.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1:ℝ)<3)
      (by norm_num : -(1/4:ℝ)<0)).le
  have hb0 (j) : 0 ≤ b j := by
    have hg0 := M.shellPrefix.gamma_pos.le
    dsimp only [b,nativeFullResponse64FutureTerm]
    positivity
  have hb : Summable b := by
    have hh := (native_full_response_rows64_future_summable M.gamma ((height:ℝ)+15) 15 0
      M.shellPrefix.gamma_pos.le hg).mul_left 4
    simpa only [Nat.zero_add] using hh
  have hnorm (j) : eLpNorm (f j) 64 μ ≤ ENNReal.ofReal (b j) :=
    upper_cell_future_weighted_term_L64 M h hM hg n hpast height j weights hw
  have hbudget : (∑' j, eLpNorm (f j) 64 μ) ≤ ENNReal.ofReal (∑' j, b j) := by
    rw [ENNReal.ofReal_tsum_of_nonneg hb0 hb]
    exact ENNReal.tsum_le_tsum hnorm
  have hfinite : (∑' j, eLpNorm (f j) 64 μ) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbudget
  have hsum := summable_norm_of_tsum_eLpNorm_ne_top (by norm_num : (1:ℝ≥0∞)≤64) hfinite
  have heq : ∀ᵐ ω ∂μ, upperCellFutureHistory M n height weights ω =
      ENNReal.ofReal (∑' j, f j ω) := by
    filter_upwards [hsum] with ω hω
    rw [ENNReal.ofReal_tsum_of_nonneg (fun j => hf0 j ω) (Summable.of_norm hω)]
    apply tsum_congr
    intro j
    rw [ENNReal.ofReal_mul (upper_cell_history_weight_nonneg j),
      ENNReal.ofReal_toReal (upper_cell_future_depth_max_ne_top M n height j weights ω)]
  have hreal : (fun ω => (upperCellFutureHistory M n height weights ω).toReal)
      =ᵐ[μ] (fun ω => ∑' j,f j ω) := heq.mono fun ω hω => by
    dsimp only
    rw [hω,ENNReal.toReal_ofReal (tsum_nonneg (fun j => hf0 j ω))]
  constructor
  · rw [eLpNorm_congr_ae hreal]
    have hh := (eLpNorm_tsum_le_of_finite μ 64 (by norm_num) f hf hfinite).trans hbudget
    simpa only [b,tsum_mul_left] using hh
  · exact heq.mono fun ω hω => by rw [hω]; exact ENNReal.ofReal_lt_top

end
end ASDExplicitGamma.Scalar
