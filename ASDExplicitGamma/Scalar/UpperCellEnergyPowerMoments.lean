module

public import ASDExplicitGamma.Native.OldSignedL2ProductExpectation

/-! Power moments for the correlated fresh-band sensitivity payment. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- A finite norm cap gives the L2 cap of each nonnegative integer power.
This retains the original random variable, rather than an independent copy. -/
theorem upper_cell_power_L2 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (F : Ω → ℝ) (j : ℕ) (hj : 0 < j) (c : ℝ)
    (hF : AEStronglyMeasurable F μ) (hF0 : ∀ ω, 0 ≤ F ω) (hc : 0 ≤ c)
    (hcap : eLpNorm F (2*(j:ℝ≥0∞)) μ ≤ ENNReal.ofReal c) :
    MemLp (fun ω => F ω^j) 2 μ ∧ lpNorm (fun ω => F ω^j) 2 μ ≤ c^j := by
  have hid : eLpNorm (fun ω => F ω^j) 2 μ =
      (eLpNorm F (2*(j:ℝ≥0∞)) μ)^j := by
    have hh := eLpNorm_norm_rpow (p := (2:ℝ≥0∞)) F hF
      (show 0 < (j:ℝ) by exact_mod_cast hj)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hF0 _), Real.rpow_natCast,
      ENNReal.ofReal_natCast, ENNReal.rpow_natCast] using hh
  have hbound : eLpNorm (fun ω => F ω^j) 2 μ ≤ ENNReal.ofReal (c^j) := by
    rw [hid, ENNReal.ofReal_pow hc]
    exact pow_le_pow_left' hcap j
  have hmem : MemLp (fun ω => F ω^j) 2 μ :=
    hbound.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hmem,?_⟩
  rw [lpNorm]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq
    (ENNReal.toReal_ofReal (pow_nonneg hc j))

/-- On a probability space, the same L6 cap controls all three powers used
by the cubic sensitivity envelope. -/
theorem upper_cell_sensitivity_power_L2 {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω → ℝ)
    (hF : AEStronglyMeasurable F μ) (hF0 : ∀ ω, 0 ≤ F ω)
    (c : ℝ) (hc : 0 ≤ c) (hcap : eLpNorm F 6 μ ≤ ENNReal.ofReal c)
    (j : ℕ) (hj : 0 < j) (hj3 : j ≤ 3) :
    MemLp (fun ω => F ω^j) 2 μ ∧ lpNorm (fun ω => F ω^j) 2 μ ≤ c^j := by
  apply upper_cell_power_L2 μ F j hj c hF hF0 hc
  refine (eLpNorm_le_eLpNorm_of_exponent_le ?_).trans hcap
  have hcast : (j:ℝ≥0∞) ≤ 3 := by exact_mod_cast hj3
  calc 2*(j:ℝ≥0∞) ≤ 2*3 := mul_le_mul' le_rfl hcast
       _ = 6 := by norm_num

end
end ASDExplicitGamma.Scalar
