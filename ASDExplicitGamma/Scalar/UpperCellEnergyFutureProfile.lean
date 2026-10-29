module

public import ASDExplicitGamma.Scalar.UpperCellEnergyFutureHistory
public import ASDExplicitGamma.Numerics.Scalar.Frames

/-! The complete actual full-response history obeys the literal UPPER
m_new profile, with both S0 and S1 and the finite frame denominator. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Algsuperdiff.Section3 Native
open ASDExplicitGamma.Numerics.Inverse ASDExplicitGamma.Numerics.Scalar
noncomputable section

/-- Sum the complete future profile before comparing its physical frame
factor to the geometric majorant. -/
theorem upper_cell_future_sum_profile (gamma height : ℝ)
    (hg0 : 0 ≤ gamma) (hg : gamma ≤ gammaZero) (hh0 : 0 ≤ height)
    (hb : gamma*height ≤ 17/50) :
    4*(∑' j : ℕ, nativeFullResponse64FutureTerm gamma (height+15) 15 j) ≤
      upperCellHistoryProfile gamma (gamma*height) := by
  let C := (1009309/500000:ℝ)+gamma*(16684*(height+15)+5899542)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have ht := native_full_response_rows64_future_tail gamma (height+15) 15 0 hg0 hg (by positivity)
  simp only [Nat.zero_add,Nat.cast_zero,add_zero,pow_zero,one_mul] at ht
  have hc := native_full_response_rows64_coefficients
  have hcoeff : C*(invS0:ℝ)+gamma*16684*(invS1:ℝ) ≤
      C*(1130469/1000000:ℝ)+gamma*16684*(838143/200000:ℝ) :=
    add_le_add (mul_le_mul_of_nonneg_left hc.2.2.2.1.le hC)
      (mul_le_mul_of_nonneg_left hc.2.2.2.2.le (mul_nonneg hg0 (by norm_num)))
  have hout : 0 ≤ C*(1130469/1000000:ℝ)+gamma*16684*(838143/200000:ℝ) := by positivity
  have hexp : 2*gamma*(height+15)+2*gamma*15 = 2*(gamma*height)+60*gamma := by ring
  have hd := upper_cell_profile_denominator_pos gamma (gamma*height) hg hb
  have hpow := three_power_le_geometric (2*(gamma*height)+60*gamma)
    (by positivity) (by linarith only [hd])
  calc
    _ ≤ 4*((C*(invS0:ℝ)+gamma*16684*(invS1:ℝ))*
        (3:ℝ)^(2*gamma*(height+15)+2*gamma*15)) :=
      mul_le_mul_of_nonneg_left ht (by norm_num)
    _ ≤ 4*((C*(1130469/1000000:ℝ)+gamma*16684*(838143/200000:ℝ))*
        (1/(1-(11/10:ℝ)*(2*(gamma*height)+60*gamma)))) := by
      rw [hexp]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul hcoeff hpow (Real.rpow_nonneg (by norm_num) _) hout) (by norm_num)
    _ = _ := by unfold upperCellHistoryProfile; dsimp only [C]; ring

/-- The actual complete terminal full-response history is bounded by m_new
and is finite almost surely. All bank and reset inputs are discharged from
the completed past; no inverse-only history is substituted. -/
theorem upper_cell_future_history_profile
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ)
    (hpast : ∀ k < n, nativeInductionState M h k)
    (height : ℕ) (hb : M.gamma*(height:ℝ) ≤ 17/50) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc n (n+(height:ℤ)), 0 ≤ weights k ∧ weights k ≤ 1) :
    eLpNorm (fun ω => (upperCellFutureHistory M n height weights ω).toReal) 64
      (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (upperCellHistoryProfile M.gamma (M.gamma*(height:ℝ))) ∧
    (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      upperCellFutureHistory M n height weights ω < ⊤) := by
  have hh := upper_cell_future_history_L64 M h hM hg n hpast height weights hw
  exact ⟨hh.1.trans (ENNReal.ofReal_le_ofReal
    (upper_cell_future_sum_profile M.gamma height M.shellPrefix.gamma_pos.le hg
      (Nat.cast_nonneg _) hb)),hh.2⟩

end
end ASDExplicitGamma.Scalar
