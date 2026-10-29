module

public import ASDExplicitGamma.Native.HeatRemainderHolder
public import ASDExplicitGamma.Native.HeatVHEATBounds

/-! Exact conversion of the correlated Holder bound to VHEAT's J envelope. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- The top Holder interpolation factor is precisely the source ratio power. -/
theorem heat_remainder_interpolation_power_identity
    (X F a : ℝ) (hX : 0 < X) (hF : 0 ≤ F) :
    (X^(1-a)*F^a)^20=X^20*(F/X)^(20*a) := by
  rw [mul_pow,←Real.rpow_natCast,←Real.rpow_natCast,
    ←Real.rpow_mul hX.le,←Real.rpow_mul hF]
  norm_num only [Nat.cast_ofNat]
  rw [show (1-a)*(20:ℝ)=20-20*a by ring,
    show a*(20:ℝ)=20*a by ring,
    Real.rpow_sub hX,Real.div_rpow hF hX.le, Real.rpow_ofNat]
  ring

/-- The complete top-degree extended bound has exactly VHEAT's finite
real coefficient, including the generalized-Holder ratio power. -/
theorem heat_remainder_top_envelope_identity
    (e X F : ℝ) (he : 0 ≤ e) (hX : 0 < X) (hF : 0 ≤ F) (j : Fin 2) :
    (ENNReal.ofReal e)^(j.val+1)*
      ((ENNReal.ofReal X)^(1-((j.val+1:ℕ):ℝ)/108)*
        (ENNReal.ofReal F)^(((j.val+1:ℕ):ℝ)/108))^20=
      ENNReal.ofReal (nativeHeatVHEATJ e X F 20 (j.val+1) 20) := by
  have ha0 : 0 ≤ ((j.val+1:ℕ):ℝ)/108 := by positivity
  have ha1 : 0 ≤ 1-((j.val+1:ℕ):ℝ)/108 := by fin_cases j <;> norm_num
  rw [←ENNReal.ofReal_pow he,
    ENNReal.ofReal_rpow_of_nonneg hX.le ha1,
    ENNReal.ofReal_rpow_of_nonneg hF ha0,
    ←ENNReal.ofReal_mul (Real.rpow_nonneg hX.le _),
    ←ENNReal.ofReal_pow (mul_nonneg (Real.rpow_nonneg hX.le _) (Real.rpow_nonneg hF _)),
    ←ENNReal.ofReal_mul (pow_nonneg he _),heat_remainder_interpolation_power_identity X F _ hX hF,
    nativeHeatVHEATJ_top]
  congr 1
  have hexp : (20:ℝ)*(((j.val+1:ℕ):ℝ)/108)=
      (((j.val+1)*20:ℕ):ℝ)/((128-20:ℕ):ℝ) := by push_cast; ring
  rw [hexp]
  exact (mul_assoc _ _ _).symm

/-- The zero trace degree still pays the actual rare moment. -/
theorem heat_remainder_rare_power_zero
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R : Ω → ℝ) (hR : AEStronglyMeasurable R μ) (hR0 : ∀ ω,0 ≤ R ω)
    (j : Fin 2) (e : ℝ≥0∞) (hRc : eLpNorm' R 128 μ ≤ e) :
    eLpNorm' (fun ω => R ω^(j.val+1)) 1 μ ≤ e^(j.val+1) := by
  rw [heat_remainder_prime_nat_power μ R hR0 _ _ (by omega), one_mul]
  apply pow_le_pow_left'
  exact (eLpNorm'_le_eLpNorm'_of_exponent_le
    (by positivity) (by fin_cases j <;> norm_num) μ hR).trans hRc

/-- All VHEAT rare monomials, including degree zero and the interpolated
endpoint, are controlled on the joint law without independence assumptions. -/
theorem heat_remainder_rare_monomial_le_J
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R T : Ω → ℝ) (hR : AEStronglyMeasurable R μ) (hT : AEStronglyMeasurable T μ)
    (hR0 : ∀ ω,0 ≤ R ω) (hT0 : ∀ ω,0 ≤ T ω)
    (j : Fin 2) (l : ℕ) (hl : l ≤ 20)
    (e X F : ℝ) (he : 0 ≤ e) (hX : 0 < X) (hF : 0 ≤ F)
    (hRc : eLpNorm' R 128 μ ≤ ENNReal.ofReal e)
    (h20 : eLpNorm' T 20 μ ≤ ENNReal.ofReal X)
    (h128 : eLpNorm' T 128 μ ≤ ENNReal.ofReal F) :
    eLpNorm' (fun ω => R ω^(j.val+1)*T ω^l) 1 μ ≤
      ENNReal.ofReal (nativeHeatVHEATJ e X F 20 (j.val+1) l) := by
  by_cases htop : l = 20
  · subst l
    exact (heat_remainder_rare_power_top μ R T hR hT hR0 hT0 j _ _ _ hRc h20 h128).trans_eq
      (heat_remainder_top_envelope_identity e X F he hX hF j)
  have hlt : l < 20 := by omega
  rw [nativeHeatVHEATJ_of_lt _ _ _ _ _ _ hlt,
    ENNReal.ofReal_mul (pow_nonneg he _), ENNReal.ofReal_pow he,
    ENNReal.ofReal_pow hX.le]
  by_cases hl0 : l = 0
  · subst l
    simpa only [pow_zero,mul_one] using heat_remainder_rare_power_zero μ R hR hR0 j _ hRc
  exact heat_remainder_rare_power_below_top μ R T hR hT hR0 hT0 j l
    (by omega) hlt _ _ hRc h20

end
end ASDExplicitGamma.Native
