module

public import ASDExplicitGamma.Native.HeatRemainderControlHolder
public import Mathlib.Analysis.MeanInequalities

/-! Mixed powers of a child trace and the actual child average, with the
same correlated rare inverse weight. Total trace degree is preserved. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory
open scoped ENNReal
noncomputable section

private theorem heat_weighted_nat_power (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (a b : ℕ) (hk : 0 < a + b) :
    x ^ a * y ^ b ≤ (a : ℝ) / ((a + b : ℕ) : ℝ) * x ^ (a + b) +
      (b : ℝ) / ((a + b : ℕ) : ℝ) * y ^ (a + b) := by
  have hkR : 0 < ((a + b : ℕ) : ℝ) := by exact_mod_cast hk
  have hw : (a : ℝ) / ((a + b : ℕ) : ℝ) + (b : ℝ) / ((a + b : ℕ) : ℝ) = 1 := by
    rw [← add_div]
    simpa only [Nat.cast_add] using div_self hkR.ne'
  have hh := Real.geom_mean_le_arith_mean2_weighted
    (div_nonneg (Nat.cast_nonneg a) hkR.le) (div_nonneg (Nat.cast_nonneg b) hkR.le)
    (pow_nonneg hx (a + b)) (pow_nonneg hy (a + b)) hw
  have he (z : ℝ) (hz : 0 ≤ z) (j : ℕ) :
      (z ^ (a + b)) ^ ((j : ℝ) / ((a + b : ℕ) : ℝ)) = z ^ j := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hz]
    rw [mul_div_cancel₀ _ hkR.ne', Real.rpow_natCast]
  simpa only [he x hx a, he y hy b] using hh

/-- Generalized Holder pays the child/average mixed powers by their TOTAL
trace degree, even with an arbitrarily correlated rare inverse weight. This
is the estimate used for every mixed term in the complete VHEAT error. -/
theorem nativeHeat_correlated_rare_mixed_product_le_J
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R A T : Ω → ℝ)
    (hR : AEStronglyMeasurable R μ) (hA : AEStronglyMeasurable A μ)
    (hT : AEStronglyMeasurable T μ)
    (hR0 : ∀ ω, 0 ≤ R ω) (hA0 : ∀ ω, 0 ≤ A ω) (hT0 : ∀ ω, 0 ≤ T ω)
    (ε X F : ℝ) (hε : 0 ≤ ε) (hX : 0 < X) (hF : 0 ≤ F)
    (hR128 : eLpNorm R 128 μ ≤ ENNReal.ofReal ε)
    (hA20 : eLpNorm A 20 μ ≤ ENNReal.ofReal X)
    (hT20 : eLpNorm T 20 μ ≤ ENNReal.ofReal X)
    (hA128 : eLpNorm A 128 μ ≤ ENNReal.ofReal F)
    (hT128 : eLpNorm T 128 μ ≤ ENNReal.ofReal F)
    (j a b : ℕ) (hj : j ≤ 2) (hab : a + b ≤ 20) :
    Integrable (fun ω => R ω ^ j * (A ω ^ a * T ω ^ b)) μ ∧
      (∫ ω, R ω ^ j * (A ω ^ a * T ω ^ b) ∂μ) ≤ nativeHeatVHEATJ ε X F 20 j (a + b) := by
  have hAcap := nativeHeat_correlated_rare_product_le_J μ R A hR hA hR0 hA0
    ε X F hε hX hF hR128 hA20 hA128 j (a+b) hj hab
  have hTcap := nativeHeat_correlated_rare_product_le_J μ R T hR hT hR0 hT0
    ε X F hε hX hF hR128 hT20 hT128 j (a+b) hj hab
  by_cases hk0 : a + b = 0
  · have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst a
    subst b
    simpa only [pow_zero, mul_one, zero_add] using hAcap
  have hk : 0 < a + b := Nat.pos_of_ne_zero hk0
  let c : ℝ := (a : ℝ) / ((a + b : ℕ) : ℝ)
  let d : ℝ := (b : ℝ) / ((a + b : ℕ) : ℝ)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hcd : c + d = 1 := by
    dsimp [c, d]
    rw [← add_div]
    push_cast
    exact div_self (by exact_mod_cast hk.ne')
  have hbound (ω : Ω) : R ω ^ j * (A ω ^ a * T ω ^ b) ≤
      c * (R ω ^ j * A ω ^ (a+b)) + d * (R ω ^ j * T ω ^ (a+b)) := by
    have hh := mul_le_mul_of_nonneg_left (heat_weighted_nat_power (A ω) (T ω) (hA0 ω) (hT0 ω) a b hk)
      (pow_nonneg (hR0 ω) j)
    convert hh using 1 <;> dsimp [c,d] <;> ring
  have hsm : AEStronglyMeasurable (fun ω => R ω ^ j * (A ω ^ a * T ω ^ b)) μ :=
    (hR.pow j).mul ((hA.pow a).mul (hT.pow b))
  have hnn (ω : Ω) : 0 ≤ R ω ^ j * (A ω ^ a * T ω ^ b) :=
    mul_nonneg (pow_nonneg (hR0 ω) j) (mul_nonneg (pow_nonneg (hA0 ω) a) (pow_nonneg (hT0 ω) b))
  have hi := (hAcap.1.const_mul c).add (hTcap.1.const_mul d)
  have hm : Integrable (fun ω => R ω ^ j * (A ω ^ a * T ω ^ b)) μ :=
    hi.mono' hsm (ae_of_all μ fun ω => by rw [Real.norm_of_nonneg (hnn ω)]; exact hbound ω)
  refine ⟨hm, ?_⟩
  calc
    _ ≤ ∫ ω, c * (R ω ^ j * A ω ^ (a+b)) + d * (R ω ^ j * T ω ^ (a+b)) ∂μ :=
      integral_mono hm hi hbound
    _ = c * (∫ ω, R ω ^ j * A ω ^ (a+b) ∂μ) + d * (∫ ω, R ω ^ j * T ω ^ (a+b) ∂μ) := by
      rw [integral_add (hAcap.1.const_mul c) (hTcap.1.const_mul d), integral_const_mul, integral_const_mul]
    _ ≤ c * nativeHeatVHEATJ ε X F 20 j (a+b) + d * nativeHeatVHEATJ ε X F 20 j (a+b) :=
      add_le_add (mul_le_mul_of_nonneg_left hAcap.2 hc) (mul_le_mul_of_nonneg_left hTcap.2 hd)
    _ = nativeHeatVHEATJ ε X F 20 j (a+b) := by rw [← add_mul, hcd, one_mul]

end
end ASDExplicitGamma.Native
