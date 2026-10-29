module

public import ASDExplicitGamma.Native.HeatVHEATBounds
public import ASDExplicitGamma.Gaussian.GaussMomentHolder
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-! Correlated generalized Holder with the source exponents 128 and 20.
The top-degree interpolation retains the precise raw-profile exponent; no
independence of a rare inverse weight and its trace is required. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory
open scoped ENNReal
noncomputable section

private theorem heat_norm_moment {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) (hf : AEStronglyMeasurable f μ) (p : ℕ) (hp : 0 < p) :
    (∫⁻ ω, ‖f ω‖ₑ ^ p ∂μ) = eLpNorm f (p : ℝ≥0∞) μ ^ p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by exact_mod_cast hp.ne') (by finiteness) hf]
  simp only [ENNReal.toReal_natCast]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  rw [one_div_mul_cancel hpR.ne', ENNReal.rpow_one]
  simp only [ENNReal.rpow_natCast]

/-- The precise three-factor Holder estimate behind the VHEAT rare products.
It is valid for arbitrarily correlated factors; the exponent balance is the
literal generalized Holder balance. -/
theorem nativeHeat_correlated_three_norm_powers
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f g h : Ω → ℝ)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hh : AEStronglyMeasurable h μ)
    (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hbalance : a / 128 + b / 20 + c / 128 = 1) :
    (∫⁻ ω, ‖f ω‖ₑ ^ a * ‖g ω‖ₑ ^ b * ‖h ω‖ₑ ^ c ∂μ) ≤
      eLpNorm f 128 μ ^ a * eLpNorm g 20 μ ^ b * eLpNorm h 128 μ ^ c := by
  let u : Fin 3 → Ω → ℝ≥0∞ := ![fun ω => ‖f ω‖ₑ ^ (128 : ℕ),
    fun ω => ‖g ω‖ₑ ^ (20 : ℕ), fun ω => ‖h ω‖ₑ ^ (128 : ℕ)]
  let w : Fin 3 → ℝ := ![a / 128, b / 20, c / 128]
  have hw : ∑ i : Fin 3, w i = 1 := by simpa [w, Fin.sum_univ_succ, add_assoc] using hbalance
  have hw0 : ∀ i ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ w i := by
    intro i hi
    fin_cases i <;> simp [w] <;> positivity
  have hu : ∀ i ∈ (Finset.univ : Finset (Fin 3)), AEMeasurable (u i) μ := by
    intro i hi
    fin_cases i
    · exact hf.enorm.pow_const _
    · exact hg.enorm.pow_const _
    · exact hh.enorm.pow_const _
  have hp := ENNReal.lintegral_prod_norm_pow_le Finset.univ hu hw hw0
  have hreduce (x : ℝ≥0∞) (p : ℕ) (e : ℝ) (hp0 : 0 < p) :
      (x ^ p) ^ (e / (p : ℝ)) = x ^ e := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    congr 1
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp0.ne'
    field_simp
  simp only [Fin.prod_univ_three] at hp
  change (∫⁻ ω, (‖f ω‖ₑ ^ (128 : ℕ)) ^ (a / 128) *
      (‖g ω‖ₑ ^ (20 : ℕ)) ^ (b / 20) * (‖h ω‖ₑ ^ (128 : ℕ)) ^ (c / 128) ∂μ) ≤
    (∫⁻ ω, ‖f ω‖ₑ ^ (128 : ℕ) ∂μ) ^ (a / 128) *
      (∫⁻ ω, ‖g ω‖ₑ ^ (20 : ℕ) ∂μ) ^ (b / 20) *
      (∫⁻ ω, ‖h ω‖ₑ ^ (128 : ℕ) ∂μ) ^ (c / 128) at hp
  have h128 (x : ℝ≥0∞) (e : ℝ) : (x ^ (128 : ℕ)) ^ (e / 128) = x ^ e := by
    simpa only [Nat.cast_ofNat] using hreduce x 128 e (by norm_num)
  have h20 (x : ℝ≥0∞) (e : ℝ) : (x ^ (20 : ℕ)) ^ (e / 20) = x ^ e := by
    simpa only [Nat.cast_ofNat] using hreduce x 20 e (by norm_num)
  simp only [h128, h20] at hp
  rw [heat_norm_moment μ f hf 128 (by norm_num), heat_norm_moment μ g hg 20 (by norm_num),
    heat_norm_moment μ h hh 128 (by norm_num)] at hp
  simpa only [h128, h20, mul_assoc, Nat.cast_ofNat] using hp

/-- Every below-top rare product has its ordinary VHEAT envelope. The slack
in the exponent balance is paid by the constant function on a probability
space, so orders one and two of the rare weight are both retained. -/
theorem nativeHeat_correlated_rare_below_top_lintegral
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R T : Ω → ℝ) (hR : AEStronglyMeasurable R μ) (hT : AEStronglyMeasurable T μ)
    (ε X : ℝ) (hε : 0 ≤ ε) (hX : 0 ≤ X)
    (hRcap : eLpNorm R 128 μ ≤ ENNReal.ofReal ε)
    (hTcap : eLpNorm T 20 μ ≤ ENNReal.ofReal X)
    (j l : ℕ) (hj : j ≤ 2) (hl : l < 20) :
    (∫⁻ ω, ‖R ω‖ₑ ^ j * ‖T ω‖ₑ ^ l ∂μ) ≤ ENNReal.ofReal (ε ^ j * X ^ l) := by
  have hjR : (j : ℝ) ≤ 2 := by exact_mod_cast hj
  have hlR : (l : ℝ) ≤ 19 := by exact_mod_cast (show l ≤ 19 by omega)
  let c : ℝ := 128 - (j : ℝ) - 128 * (l : ℝ) / 20
  have hc : 0 ≤ c := by dsimp [c]; linarith
  have hb : (j : ℝ) / 128 + (l : ℝ) / 20 + c / 128 = 1 := by dsimp [c]; ring
  have hh := nativeHeat_correlated_three_norm_powers μ R T (fun _ => 1)
    hR hT aestronglyMeasurable_const (j : ℝ) (l : ℝ) c
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) hc hb
  have hconst : eLpNorm (fun _ : Ω => (1 : ℝ)) 128 μ = 1 := by
    rw [eLpNorm_const' _ (by norm_num) (by norm_num)]
    simp
  simp only [enorm_one, ENNReal.one_rpow, mul_one, hconst, ENNReal.rpow_natCast] at hh
  exact hh.trans (by
    calc
      eLpNorm R 128 μ ^ j * eLpNorm T 20 μ ^ l ≤
          ENNReal.ofReal ε ^ j * ENNReal.ofReal X ^ l :=
        mul_le_mul' (pow_le_pow_left' hRcap j) (pow_le_pow_left' hTcap l)
      _ = ENNReal.ofReal (ε ^ j * X ^ l) := by
        rw [← ENNReal.ofReal_pow hε, ← ENNReal.ofReal_pow hX,
          ENNReal.ofReal_mul (pow_nonneg hε j)])

/-- At degree twenty the exact interpolation loss is `j*20/108`. Both trace
norms belong to the same function; the estimate permits arbitrary correlation
with the rare inverse weight. -/
theorem nativeHeat_correlated_rare_top_lintegral
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (R T : Ω → ℝ) (hR : AEStronglyMeasurable R μ) (hT : AEStronglyMeasurable T μ)
    (ε X F : ℝ) (hε : 0 ≤ ε) (hX : 0 < X) (hF : 0 ≤ F)
    (hRcap : eLpNorm R 128 μ ≤ ENNReal.ofReal ε)
    (hTcap : eLpNorm T 20 μ ≤ ENNReal.ofReal X)
    (hFcap : eLpNorm T 128 μ ≤ ENNReal.ofReal F)
    (j : ℕ) (hj : j ≤ 2) :
    (∫⁻ ω, ‖R ω‖ₑ ^ j * ‖T ω‖ₑ ^ (20 : ℕ) ∂μ) ≤
      ENNReal.ofReal (nativeHeatVHEATJ ε X F 20 j 20) := by
  let a : ℝ := (j : ℝ) * 20 / 108
  have hjR : (j : ℝ) ≤ 2 := by exact_mod_cast hj
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ 20 - a := by dsimp [a]; linarith
  have hbalance : (j : ℝ) / 128 + (20 - a) / 20 + a / 128 = 1 := by dsimp [a]; ring
  have hh := nativeHeat_correlated_three_norm_powers μ R T T hR hT hT
    (j : ℝ) (20 - a) a (Nat.cast_nonneg _) hb ha hbalance
  have he (ω : Ω) : ‖R ω‖ₑ ^ (j : ℝ) * ‖T ω‖ₑ ^ (20 - a) * ‖T ω‖ₑ ^ a =
      ‖R ω‖ₑ ^ j * ‖T ω‖ₑ ^ (20 : ℕ) := by
    rw [mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ hb ha]
    simp only [sub_add_cancel, ENNReal.rpow_natCast]
    norm_num
  simp only [he] at hh
  have hcaps := mul_le_mul'
    (mul_le_mul' (ENNReal.rpow_le_rpow hRcap (Nat.cast_nonneg j))
      (ENNReal.rpow_le_rpow hTcap hb)) (ENNReal.rpow_le_rpow hFcap ha)
  have hidentity : ε ^ j * X ^ (20 - a) * F ^ a = nativeHeatVHEATJ ε X F 20 j 20 := by
    simp only [nativeHeatVHEATJ, lt_self_iff_false, ↓reduceIte]
    have hexp : (((j * 20 : ℕ) : ℝ) / ((128 - 20 : ℕ) : ℝ)) = a := by
      norm_num [a]
    rw [hexp]
    have hdiv : Real.rpow (F / X) a = F ^ a / X ^ a := Real.div_rpow hF hX.le a
    rw [hdiv, Real.rpow_sub hX _ _]
    have hp20 : X ^ (20 : ℝ) = X ^ (20 : ℕ) := by
      simpa only [Nat.cast_ofNat] using Real.rpow_natCast X 20
    rw [hp20]
    field_simp [ne_of_gt (Real.rpow_pos_of_pos hX a)]
  have hcapEq : ENNReal.ofReal ε ^ (j : ℝ) * ENNReal.ofReal X ^ (20 - a) *
      ENNReal.ofReal F ^ a = ENNReal.ofReal (nativeHeatVHEATJ ε X F 20 j 20) := by
    rw [ENNReal.rpow_natCast, ← ENNReal.ofReal_pow hε,
      ENNReal.ofReal_rpow_of_nonneg hX.le hb, ENNReal.ofReal_rpow_of_nonneg hF ha,
      ← ENNReal.ofReal_mul (pow_nonneg hε j),
      ← ENNReal.ofReal_mul (mul_nonneg (pow_nonneg hε j) (Real.rpow_nonneg hX.le _)), hidentity]
  exact hh.trans (hcaps.trans_eq hcapEq)

/-- VHEAT (9) as an actual correlated integral estimate, including
integrability. The only norm inputs are the rare L128 profile and the two
trace profiles; the desired product bound is never a premise. -/
theorem nativeHeat_correlated_rare_product_le_J
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R T : Ω → ℝ) (hR : AEStronglyMeasurable R μ) (hT : AEStronglyMeasurable T μ)
    (hR0 : ∀ ω, 0 ≤ R ω) (hT0 : ∀ ω, 0 ≤ T ω)
    (ε X F : ℝ) (hε : 0 ≤ ε) (hX : 0 < X) (hF : 0 ≤ F)
    (hRcap : eLpNorm R 128 μ ≤ ENNReal.ofReal ε)
    (hTcap : eLpNorm T 20 μ ≤ ENNReal.ofReal X)
    (hFcap : eLpNorm T 128 μ ≤ ENNReal.ofReal F)
    (j l : ℕ) (hj : j ≤ 2) (hl : l ≤ 20) :
    Integrable (fun ω => R ω ^ j * T ω ^ l) μ ∧
      (∫ ω, R ω ^ j * T ω ^ l ∂μ) ≤ nativeHeatVHEATJ ε X F 20 j l := by
  have hn : (∫⁻ ω, ‖R ω‖ₑ ^ j * ‖T ω‖ₑ ^ l ∂μ) ≤
      ENNReal.ofReal (nativeHeatVHEATJ ε X F 20 j l) := by
    by_cases hlt : l < 20
    · simpa only [nativeHeatVHEATJ, ite_eq_left hlt] using
        nativeHeat_correlated_rare_below_top_lintegral μ R T hR hT ε X hε hX.le hRcap hTcap j l hj hlt
    · have he : l = 20 := by omega
      subst l
      exact nativeHeat_correlated_rare_top_lintegral μ R T hR hT ε X F hε hX hF hRcap hTcap hFcap j hj
  have he (ω : Ω) : ENNReal.ofReal (R ω ^ j * T ω ^ l) = ‖R ω‖ₑ ^ j * ‖T ω‖ₑ ^ l := by
    rw [ENNReal.ofReal_mul (pow_nonneg (hR0 ω) j), ENNReal.ofReal_pow (hR0 ω),
      ENNReal.ofReal_pow (hT0 ω), Real.enorm_eq_ofReal (hR0 ω), Real.enorm_eq_ofReal (hT0 ω)]
  have hsm : AEStronglyMeasurable (fun ω => R ω ^ j * T ω ^ l) μ := (hR.pow j).mul (hT.pow l)
  have hn0 (ω : Ω) : 0 ≤ R ω ^ j * T ω ^ l := mul_nonneg (pow_nonneg (hR0 ω) j) (pow_nonneg (hT0 ω) l)
  have hn' : (∫⁻ ω, ENNReal.ofReal (R ω ^ j * T ω ^ l) ∂μ) ≤
      ENNReal.ofReal (nativeHeatVHEATJ ε X F 20 j l) := by simpa only [he] using hn
  have hmem : MemLp (fun ω => R ω ^ j * T ω ^ l) 1 μ := by
    rw [memLp_iff, eLpNorm_one_eq_lintegral_enorm hsm]
    simp only [Real.enorm_eq_ofReal (hn0 _)]
    exact lt_of_le_of_lt hn' ENNReal.ofReal_lt_top
  refine ⟨memLp_one_iff_integrable.mp hmem, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all μ hn0) hsm]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hn').trans_eq
    (ENNReal.toReal_ofReal (nativeHeatVHEATJ_nonneg ε X F 20 j l hε hX hF))

end
end ASDExplicitGamma.Native
