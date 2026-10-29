module

public import ASDExplicitGamma.Native.HeatRemainderMoments

/-! Mixed child/average products in the VHEAT descendant bracket. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- Two positive trace powers use their total trace degree in Hölder. -/
theorem heat_remainder_mixed_power_holder
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Y T : Ω → ℝ)
    (hY : AEStronglyMeasurable Y μ) (hT : AEStronglyMeasurable T μ)
    (hY0 : ∀ ω,0 ≤ Y ω) (hT0 : ∀ ω,0 ≤ T ω)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (r : ℝ) (hr : 0 < r) :
    eLpNorm' (fun ω => Y ω^a*T ω^b) r μ ≤
      eLpNorm' Y (r*((a+b:ℕ):ℝ)) μ^a * eLpNorm' T (r*((a+b:ℕ):ℝ)) μ^b := by
  have haR : 0 < (a:ℝ) := by exact_mod_cast ha
  have hbR : 0 < (b:ℝ) := by exact_mod_cast hb
  have habR : 0 < ((a+b:ℕ):ℝ) := by positivity
  have hp : r < r*((a+b:ℕ):ℝ)/(a:ℝ) := by
    apply (lt_div_iff₀ haR).mpr
    push_cast
    nlinarith
  have hc : 1/r = 1/(r*((a+b:ℕ):ℝ)/(a:ℝ)) +
      1/(r*((a+b:ℕ):ℝ)/(b:ℝ)) := by
    field_simp
    push_cast
    ring
  have hh := eLpNorm'_le_eLpNorm'_mul_eLpNorm'
    (f := fun ω => Y ω^a) (g := fun ω => T ω^b)
    (p := r*((a+b:ℕ):ℝ)/(a:ℝ)) (q := r*((a+b:ℕ):ℝ)/(b:ℝ)) (r := r)
    (hY.pow a) (hT.pow b) (fun x y : ℝ => x*y) 1
    (Filter.Eventually.of_forall fun _ => by simp only [nnnorm_mul,one_mul,le_refl]) hr hp hc
  have hpa : r*((a+b:ℕ):ℝ)/(a:ℝ)*(a:ℝ)=r*((a+b:ℕ):ℝ) := by field_simp
  have hqb : r*((a+b:ℕ):ℝ)/(b:ℝ)*(b:ℝ)=r*((a+b:ℕ):ℝ) := by field_simp
  simpa only [ENNReal.coe_one,one_mul,
    heat_remainder_prime_nat_power μ Y hY0 _ a ha,
    heat_remainder_prime_nat_power μ T hT0 _ b hb,hpa,hqb] using hh

/-- Baseline mixed powers use separate average and individual trace caps. -/
theorem heat_remainder_mixed_power_cap
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y T : Ω → ℝ) (hY : AEStronglyMeasurable Y μ) (hT : AEStronglyMeasurable T μ)
    (hY0 : ∀ ω,0 ≤ Y ω) (hT0 : ∀ ω,0 ≤ T ω)
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (r : ℝ) (hr : 0 < r)
    (q : ℝ) (hq : r*((a+b:ℕ):ℝ) ≤ q) (A B : ℝ≥0∞)
    (hAc : eLpNorm' Y q μ ≤ A) (hBc : eLpNorm' T q μ ≤ B) :
    eLpNorm' (fun ω => Y ω^a*T ω^b) r μ ≤ A^a*B^b := by
  have hs : 0 < r*((a+b:ℕ):ℝ) := mul_pos hr (by positivity)
  exact (heat_remainder_mixed_power_holder μ Y T hY hT hY0 hT0 a b ha hb r hr).trans
    (mul_le_mul' (pow_le_pow_left' ((eLpNorm'_le_eLpNorm'_of_exponent_le hs hq μ hY).trans hAc) a)
      (pow_le_pow_left' ((eLpNorm'_le_eLpNorm'_of_exponent_le hs hq μ hT).trans hBc) b))

/-- The mixed-power cap also covers a missing average or child factor. -/
theorem heat_remainder_mixed_power_cap_nonzero
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y T : Ω → ℝ) (hY : AEStronglyMeasurable Y μ) (hT : AEStronglyMeasurable T μ)
    (hY0 : ∀ ω,0 ≤ Y ω) (hT0 : ∀ ω,0 ≤ T ω)
    (a b : ℕ) (hab : 0 < a+b) (r : ℝ) (hr : 0 < r)
    (q : ℝ) (hq : r*((a+b:ℕ):ℝ) ≤ q) (A B : ℝ≥0∞)
    (hAc : eLpNorm' Y q μ ≤ A) (hBc : eLpNorm' T q μ ≤ B) :
    eLpNorm' (fun ω => Y ω^a*T ω^b) r μ ≤ A^a*B^b := by
  by_cases ha : a=0
  · subst a
    simp only [zero_add] at hab hq
    simp only [pow_zero,one_mul]
    rw [heat_remainder_prime_nat_power μ T hT0 _ _ hab]
    exact pow_le_pow_left' ((eLpNorm'_le_eLpNorm'_of_exponent_le
      (mul_pos hr (by exact_mod_cast hab)) hq μ hT).trans hBc) b
  by_cases hb : b=0
  · subst b
    simp only [add_zero] at hab hq
    simp only [pow_zero,mul_one]
    rw [heat_remainder_prime_nat_power μ Y hY0 _ _ hab]
    exact pow_le_pow_left' ((eLpNorm'_le_eLpNorm'_of_exponent_le
      (mul_pos hr (by exact_mod_cast hab)) hq μ hY).trans hAc) a
  exact heat_remainder_mixed_power_cap μ Y T hY hT hY0 hT0 a b
    (by omega) (by omega) r hr q hq A B hAc hBc

/-- An inverse weight and two correlated trace factors consume the same
single total-degree envelope. No spatial or probabilistic independence is used. -/
theorem heat_remainder_rare_mixed_holder
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R Y T : Ω → ℝ) (hR : AEStronglyMeasurable R μ)
    (hY : AEStronglyMeasurable Y μ) (hT : AEStronglyMeasurable T μ)
    (hR0 : ∀ ω,0 ≤ R ω) (hY0 : ∀ ω,0 ≤ Y ω) (hT0 : ∀ ω,0 ≤ T ω)
    (j : Fin 2) (a b : ℕ) (hab : 0 < a+b)
    (e A : ℝ≥0∞) (hRc : eLpNorm' R 128 μ ≤ e)
    (hYc : eLpNorm' Y (128*((a+b:ℕ):ℝ)/(128-((j.val+1:ℕ):ℝ))) μ ≤ A)
    (hTc : eLpNorm' T (128*((a+b:ℕ):ℝ)/(128-((j.val+1:ℕ):ℝ))) μ ≤ A) :
    eLpNorm' (fun ω => R ω^(j.val+1)*(Y ω^a*T ω^b)) 1 μ ≤ e^(j.val+1)*A^(a+b) := by
  let d : ℝ := ((j.val+1:ℕ):ℝ)
  have hd : 0 < d := by dsimp [d]; positivity
  have hd128 : d < 128 := by fin_cases j <;> norm_num [d]
  have hden : 0 < 128-d := sub_pos.mpr hd128
  have hc : (1:ℝ)=1/(128/d)+1/(128/(128-d)) := by field_simp; ring
  have hh := eLpNorm'_le_eLpNorm'_mul_eLpNorm'
    (f := fun ω => R ω^(j.val+1)) (g := fun ω => Y ω^a*T ω^b)
    (p := 128/d) (q := 128/(128-d)) (r := 1)
    (hR.pow _) ((hY.pow a).mul (hT.pow b)) (fun x y : ℝ => x*y) 1
    (Filter.Eventually.of_forall fun _ => by simp only [nnnorm_mul,one_mul,le_refl])
    (by norm_num) ((one_lt_div hd).mpr hd128) (by simpa using hc)
  have hid : 128/d*((j.val+1:ℕ):ℝ)=128 := by change 128/d*d=128; field_simp
  have hh' : eLpNorm' (fun ω => R ω^(j.val+1)*(Y ω^a*T ω^b)) 1 μ ≤
      eLpNorm' (fun ω => R ω^(j.val+1)) (128/d) μ *
        eLpNorm' (fun ω => Y ω^a*T ω^b) (128/(128-d)) μ := by
    simpa only [ENNReal.coe_one,one_mul] using hh
  rw [heat_remainder_prime_nat_power μ R hR0 _ _ (by omega),hid] at hh'
  have hprod := heat_remainder_mixed_power_cap_nonzero μ Y T hY hT hY0 hT0 a b hab
    (128/(128-d)) (div_pos (by norm_num) hden)
    (128*((a+b:ℕ):ℝ)/(128-d)) (by apply le_of_eq; ring) A A hYc hTc
  rw [←pow_add] at hprod
  exact hh'.trans (mul_le_mul' (pow_le_pow_left' hRc _) hprod)

end
end ASDExplicitGamma.Native
