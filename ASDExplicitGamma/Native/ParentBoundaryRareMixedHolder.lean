module

public import ASDExplicitGamma.Native.HeatVHEATBounds
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-! Correlated root-compatible Holder bounds for the parent rare term. -/

@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory
open scoped ENNReal
noncomputable section

private theorem parentRare_lintegral_norm_moment
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) (hf : AEStronglyMeasurable f μ) (p : ℕ) (hp : 0 < p) :
    (∫⁻ ω, ‖f ω‖ₑ ^ p ∂μ) = eLpNorm f (p : ℝ≥0∞) μ ^ p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by exact_mod_cast hp.ne')
    (by finiteness) hf]
  simp only [ENNReal.toReal_natCast]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  rw [one_div_mul_cancel hpR.ne', ENNReal.rpow_one]
  simp only [ENNReal.rpow_natCast]

/-- The p20-root-compatible rare Holder estimate. The factor
`(eLpNorm T 20).toReal ^ 19` is retained for both rare powers; no independence
assumption is used. -/
theorem parent_boundary_rare_mixed_product_holder
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T U R : Ω → ℝ)
    (hT0 : ∀ ω, 0 ≤ T ω) (hU0 : ∀ ω, 0 ≤ U ω) (hR0 : ∀ ω, 0 ≤ R ω)
    (hT20 : MemLp T (20 : ℝ≥0∞) μ)
    (hU128 : MemLp U (128 : ℝ≥0∞) μ)
    (hR128 : MemLp R (128 : ℝ≥0∞) μ)
    (ε F : ℝ) (hε : 0 ≤ ε) (hF : 0 ≤ F)
    (hRcap : eLpNorm R (128 : ℝ≥0∞) μ ≤ ENNReal.ofReal ε)
    (hUcap : eLpNorm U (128 : ℝ≥0∞) μ ≤ ENNReal.ofReal F)
    (j : Fin 2) :
    Integrable (fun ω => T ω ^ 19 * R ω ^ (j.val + 1) * U ω) μ ∧
      MeasureTheory.integral μ (fun ω => T ω ^ 19 * R ω ^ (j.val + 1) * U ω) ≤
        (eLpNorm T (20 : ℝ≥0∞) μ).toReal ^ 19 * ε ^ (j.val + 1) * F := by
  have hT := hT20.aestronglyMeasurable
  have hU := hU128.aestronglyMeasurable
  have hR := hR128.aestronglyMeasurable
  let a : ℕ := j.val + 1
  let d : ℝ := 128 - (a : ℝ) - 128 * (19 : ℝ) / 20 - 1
  have ha : 0 < a := by dsimp [a]; omega
  have hd : 0 ≤ d := by
    have ha2 : a ≤ 2 := by dsimp [a]; omega
    dsimp [d]
    have ha2r : (a : ℝ) ≤ 2 := by exact_mod_cast ha2
    norm_num
    linarith
  have hbalance : (a : ℝ) / 128 + (19 : ℝ) / 20 + 1 / 128 + d / 128 = 1 := by
    dsimp [d]
    ring
  let u : Fin 4 → Ω → ℝ≥0∞ := ![
    (fun ω => ‖R ω‖ₑ ^ (128 : ℕ)),
    (fun ω => ‖T ω‖ₑ ^ (20 : ℕ)),
    (fun ω => ‖U ω‖ₑ ^ (128 : ℕ)),
    (fun _ => (1 : ℝ≥0∞))]
  let w : Fin 4 → ℝ := ![(a : ℝ) / 128, (19 : ℝ) / 20, 1 / 128, d / 128]
  have hw : ∑ i : Fin 4, w i = 1 := by
    simpa [w, Fin.sum_univ_succ, add_assoc] using hbalance
  have hw0 : ∀ i ∈ (Finset.univ : Finset (Fin 4)), 0 ≤ w i := by
    intro i hi
    fin_cases i <;> simp [w] <;> positivity
  have hu : ∀ i ∈ (Finset.univ : Finset (Fin 4)), AEMeasurable (u i) μ := by
    intro i hi
    fin_cases i
    · exact hR.enorm.pow_const _
    · exact hT.enorm.pow_const _
    · exact hU.enorm.pow_const _
    · exact aemeasurable_const
  have hholder := ENNReal.lintegral_prod_norm_pow_le Finset.univ hu hw hw0
  have hreduce (x : ℝ≥0∞) (p : ℕ) (e : ℝ) (hp : 0 < p) :
      (x ^ p) ^ (e / (p : ℝ)) = x ^ e := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    congr 1
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
    field_simp
  have h128 (x : ℝ≥0∞) (e : ℝ) :
      (x ^ (128 : ℕ)) ^ (e / 128) = x ^ e := by
    simpa only [Nat.cast_ofNat] using hreduce x 128 e (by norm_num)
  have h20 (x : ℝ≥0∞) (e : ℝ) :
      (x ^ (20 : ℕ)) ^ (e / 20) = x ^ e := by
    simpa only [Nat.cast_ofNat] using hreduce x 20 e (by norm_num)
  have hOneInt : (∫⁻ ω, (1 : ℝ≥0∞) ∂μ) = 1 := by simp
  have hprodPoint (ω : Ω) :
      (∏ i : Fin 4, u i ω ^ w i) =
        ‖R ω‖ₑ ^ a * ‖T ω‖ₑ ^ (19 : ℕ) * ‖U ω‖ₑ := by
    rw [Fin.prod_univ_four]
    change (‖R ω‖ₑ ^ (128 : ℕ)) ^ ((a : ℝ) / 128) *
        (‖T ω‖ₑ ^ (20 : ℕ)) ^ ((19 : ℝ) / 20) *
        (‖U ω‖ₑ ^ (128 : ℕ)) ^ (1 / 128) *
        (1 : ℝ≥0∞) ^ (d / 128) = _
    rw [h128, h20, h128]
    simp [ENNReal.one_rpow]
  have hprodIntegral :
      (∏ i : Fin 4, (∫⁻ ω, u i ω ∂μ) ^ w i) =
        eLpNorm R (128 : ℝ≥0∞) μ ^ a *
          eLpNorm T (20 : ℝ≥0∞) μ ^ (19 : ℕ) *
          eLpNorm U (128 : ℝ≥0∞) μ := by
    rw [Fin.prod_univ_four]
    change (∫⁻ ω, ‖R ω‖ₑ ^ (128 : ℕ) ∂μ) ^ ((a : ℝ) / 128) *
        (∫⁻ ω, ‖T ω‖ₑ ^ (20 : ℕ) ∂μ) ^ ((19 : ℝ) / 20) *
        (∫⁻ ω, ‖U ω‖ₑ ^ (128 : ℕ) ∂μ) ^ (1 / 128) *
        (∫⁻ ω, (1 : ℝ≥0∞) ∂μ) ^ (d / 128) = _
    rw [parentRare_lintegral_norm_moment μ R hR 128 (by norm_num),
      parentRare_lintegral_norm_moment μ T hT 20 (by norm_num),
      parentRare_lintegral_norm_moment μ U hU 128 (by norm_num), hOneInt]
    rw [h128, h20, h128]
    simp [ENNReal.one_rpow]
  have hholder' :
      (∫⁻ ω, ‖R ω‖ₑ ^ a * ‖T ω‖ₑ ^ (19 : ℕ) * ‖U ω‖ₑ ∂μ) ≤
        eLpNorm R (128 : ℝ≥0∞) μ ^ a *
          eLpNorm T (20 : ℝ≥0∞) μ ^ (19 : ℕ) *
          eLpNorm U (128 : ℝ≥0∞) μ := by
    calc
      _ = ∫⁻ ω, ∏ i : Fin 4, u i ω ^ w i ∂μ := by
        apply lintegral_congr_ae
        exact Filter.Eventually.of_forall fun ω => (hprodPoint ω).symm
      _ ≤ ∏ i : Fin 4, (∫⁻ ω, u i ω ∂μ) ^ w i := hholder
      _ = _ := hprodIntegral
  have hpoint (ω : Ω) :
      ENNReal.ofReal (T ω ^ 19 * R ω ^ a * U ω) =
        ‖R ω‖ₑ ^ a * ‖T ω‖ₑ ^ (19 : ℕ) * ‖U ω‖ₑ := by
    rw [ENNReal.ofReal_mul (mul_nonneg (pow_nonneg (hT0 ω) 19)
      (pow_nonneg (hR0 ω) a)), ENNReal.ofReal_mul (pow_nonneg (hT0 ω) 19),
      ENNReal.ofReal_pow (hT0 ω), ENNReal.ofReal_pow (hR0 ω)]
    rw [Real.enorm_eq_ofReal (hR0 ω), Real.enorm_eq_ofReal (hT0 ω),
      Real.enorm_eq_ofReal (hU0 ω)]
    ring
  have hlin :
      (∫⁻ ω, ENNReal.ofReal (T ω ^ 19 * R ω ^ a * U ω) ∂μ) ≤
        eLpNorm R (128 : ℝ≥0∞) μ ^ a *
          eLpNorm T (20 : ℝ≥0∞) μ ^ (19 : ℕ) *
          eLpNorm U (128 : ℝ≥0∞) μ := by
    calc
      _ = ∫⁻ ω, ‖R ω‖ₑ ^ a * ‖T ω‖ₑ ^ (19 : ℕ) * ‖U ω‖ₑ ∂μ := by
        apply lintegral_congr_ae
        exact Filter.Eventually.of_forall hpoint
      _ ≤ _ := hholder'
  have hcap :
      eLpNorm R (128 : ℝ≥0∞) μ ^ a *
          eLpNorm T (20 : ℝ≥0∞) μ ^ (19 : ℕ) *
          eLpNorm U (128 : ℝ≥0∞) μ ≤
        ENNReal.ofReal ((eLpNorm T (20 : ℝ≥0∞) μ).toReal ^ 19 * ε ^ a * F) := by
    have hxTop : eLpNorm T (20 : ℝ≥0∞) μ ≠ ⊤ := hT20.eLpNorm_ne_top
    have hx : ENNReal.ofReal ((eLpNorm T (20 : ℝ≥0∞) μ).toReal) =
        eLpNorm T (20 : ℝ≥0∞) μ := ENNReal.ofReal_toReal hxTop
    have hpR : eLpNorm R (128 : ℝ≥0∞) μ ^ a ≤ ENNReal.ofReal ε ^ a :=
      pow_le_pow_left' hRcap a
    have hpU : eLpNorm U (128 : ℝ≥0∞) μ ≤ ENNReal.ofReal F := hUcap
    calc
      _ ≤ ENNReal.ofReal ε ^ a *
          eLpNorm T (20 : ℝ≥0∞) μ ^ (19 : ℕ) * ENNReal.ofReal F := by
        gcongr
      _ = ENNReal.ofReal ((eLpNorm T (20 : ℝ≥0∞) μ).toReal ^ 19 * ε ^ a * F) := by
        symm
        rw [ENNReal.ofReal_mul (mul_nonneg (pow_nonneg (ENNReal.toReal_nonneg) 19)
          (pow_nonneg hε a)), ENNReal.ofReal_mul (pow_nonneg (ENNReal.toReal_nonneg) 19),
          ENNReal.ofReal_pow (ENNReal.toReal_nonneg), ENNReal.ofReal_pow hε, hx]
        ring
  have hbound := hlin.trans hcap
  let G : Ω → ℝ := fun ω => T ω ^ 19 * R ω ^ a * U ω
  have hG0 (ω : Ω) : 0 ≤ G ω := by
    dsimp [G]
    exact mul_nonneg (mul_nonneg (pow_nonneg (hT0 ω) 19)
      (pow_nonneg (hR0 ω) a)) (hU0 ω)
  have hGsm : AEStronglyMeasurable G μ := by
    dsimp [G]
    exact (hT.pow 19).mul (hR.pow a) |>.mul hU
  have hGlin : (∫⁻ ω, ENNReal.ofReal (G ω) ∂μ) < ⊤ :=
    lt_of_le_of_lt (by simpa [G] using hbound) ENNReal.ofReal_lt_top
  have hGmem : MemLp G 1 μ := by
    rw [memLp_iff, eLpNorm_one_eq_lintegral_enorm hGsm]
    simp only [Real.enorm_eq_ofReal (hG0 _)]
    exact hGlin
  have hGint : Integrable G μ := memLp_one_iff_integrable.mp hGmem
  have hreal : MeasureTheory.integral μ G ≤
      (eLpNorm T (20 : ℝ≥0∞) μ).toReal ^ 19 * ε ^ a * F := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all μ hG0) hGsm]
    have hrealBound := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    have hB0 : 0 ≤ (eLpNorm T (20 : ℝ≥0∞) μ).toReal ^ 19 * ε ^ a * F := by
      positivity
    simpa only [ENNReal.toReal_ofReal hB0] using hrealBound
  refine ⟨?_, ?_⟩
  · simpa only [G, a] using hGint
  · simpa only [G, a] using hreal

end
end ASDExplicitGamma.Native
