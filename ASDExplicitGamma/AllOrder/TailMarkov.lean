module

public import ASDExplicitGamma.AllOrder.ObservableAdapter
public import ASDExplicitGamma.Statements.AllOrderBounds
public import ASDExplicitGamma.Numerics.AllOrder.Allocations
public import Algsuperdiff.Section3.Probability.TwoTermOrlicz
public import Algsuperdiff.Section3.Provider.Tail.TailSqrt
public import Homogenization.Probability.IndependentSums.GammaSigma.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Order.MonotoneContinuity

/-! The real-order Markov inversion used by AO-MARKOV-COUPLED. -/

@[expose] public section

open MeasureTheory
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Probability
open Homogenization.IndependentSums
open ASDExplicitGamma.Numerics.AllOrder
open scoped ENNReal

namespace ASDExplicitGamma.AllOrder

/-- The increasing polynomial gauge in the coupled Markov conversion. -/
noncomputable def allOrderTailGauge (A B x : ℝ) : ℝ := Real.exp 1 * (A * x + B * x ^ 3)

noncomputable def allOrderTailGaugeMap (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    Set.Ici (0 : ℝ) → Set.Ici (0 : ℝ) := fun x =>
  ⟨allOrderTailGauge A B x.1,
    mul_nonneg (le_of_lt (Real.exp_pos 1))
      (add_nonneg (mul_nonneg hA.le x.2) (mul_nonneg hB.le (pow_nonneg x.2 _)))⟩

theorem allOrderTailGaugeMap_strictMono (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    StrictMono (allOrderTailGaugeMap A B hA hB) := by
  intro x y hxy
  have hlinear : A * x.1 < A * y.1 := mul_lt_mul_of_pos_left hxy hA
  have hcube : x.1 ^ 3 ≤ y.1 ^ 3 := by
    exact pow_le_pow_left₀ x.2 hxy.le 3
  have hcubic : B * x.1 ^ 3 ≤ B * y.1 ^ 3 := mul_le_mul_of_nonneg_left hcube hB.le
  have hexp : 0 < Real.exp 1 := Real.exp_pos 1
  change allOrderTailGauge A B x.1 < allOrderTailGauge A B y.1
  unfold allOrderTailGauge
  nlinarith [mul_lt_mul_of_pos_left (show A*x.1 < A*y.1 by nlinarith) hexp]

theorem allOrderTailGaugeMap_surjective (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    Function.Surjective (allOrderTailGaugeMap A B hA hB) := by
  intro y
  let z := y.1 / (Real.exp 1 * A)
  have hz : 0 ≤ z := div_nonneg y.2 (mul_nonneg (le_of_lt (Real.exp_pos 1)) hA.le)
  have hden : 0 < Real.exp 1 * A := mul_pos (Real.exp_pos 1) hA
  have hupper : y.1 ≤ allOrderTailGauge A B z := by
    have hlin : Real.exp 1 * (A * z) = y.1 := by
      dsimp [z]
      field_simp
    unfold allOrderTailGauge
    have hterm : 0 ≤ Real.exp 1 * (B * z ^ 3) :=
      mul_nonneg (le_of_lt (Real.exp_pos 1)) (mul_nonneg hB.le (pow_nonneg hz _))
    nlinarith
  have hcont : ContinuousOn (fun x : ℝ => allOrderTailGauge A B x) (Set.Icc 0 z) := by
    fun_prop [allOrderTailGauge]
  have hy : allOrderTailGauge A B 0 ≤ y.1 := by
    simp [allOrderTailGauge]
    exact y.2
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc hz hcont ⟨hy, hupper⟩
  refine ⟨⟨x, hx.1⟩, ?_⟩
  apply Subtype.ext
  exact hfx

noncomputable def allOrderTailGaugeOrderIso (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    Set.Ici (0 : ℝ) ≃o Set.Ici (0 : ℝ) :=
  (allOrderTailGaugeMap_strictMono A B hA hB).orderIsoOfSurjective
    (allOrderTailGaugeMap A B hA hB) (allOrderTailGaugeMap_surjective A B hA hB)

/-- The nonnegative inverse-polynomial transform, extended to all reals by clamping. -/
noncomputable def allOrderTailInverse (A B : ℝ) (hA : 0 < A) (hB : 0 < B) (x : ℝ) : ℝ :=
  ((allOrderTailGaugeOrderIso A B hA hB).symm
    ⟨max 0 x, le_max_left _ _⟩).1

theorem allOrderTailGauge_inverse (A B : ℝ) (hA : 0 < A) (hB : 0 < B) (x : ℝ)
    (hx : 0 ≤ x) :
    allOrderTailGauge A B (allOrderTailInverse A B hA hB x) = x := by
  have harg : (⟨max 0 x, le_max_left 0 x⟩ : Set.Ici (0 : ℝ)) = ⟨x, hx⟩ := by
    apply Subtype.ext
    exact max_eq_right hx
  have hinv' : (allOrderTailGaugeOrderIso A B hA hB)
      ((allOrderTailGaugeOrderIso A B hA hB).symm ⟨x, hx⟩) = ⟨x, hx⟩ := by
    exact (allOrderTailGaugeOrderIso A B hA hB).apply_symm_apply ⟨x, hx⟩
  have hval : ((allOrderTailGaugeMap A B hA hB)
      ((allOrderTailGaugeOrderIso A B hA hB).symm ⟨x, hx⟩)).1 = x :=
    congrArg Subtype.val hinv'
  unfold allOrderTailInverse
  rw [harg]
  simpa only [allOrderTailGaugeMap] using hval

theorem allOrderTailInverse_nonneg (A B : ℝ) (hA : 0 < A) (hB : 0 < B) (x : ℝ) :
    0 ≤ allOrderTailInverse A B hA hB x :=
  ((allOrderTailGaugeOrderIso A B hA hB).symm
    ⟨max 0 x, le_max_left _ _⟩).2

theorem measurable_allOrderTailInverse (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    Measurable (allOrderTailInverse A B hA hB) := by
  apply Continuous.measurable
  unfold allOrderTailInverse
  exact continuous_subtype_val.comp <|
    (allOrderTailGaugeOrderIso A B hA hB).symm.continuous.comp <|
      Continuous.subtype_mk (continuous_const.max continuous_id) (fun x => le_max_left 0 x)

theorem allOrderTailGauge_strictMono (A B : ℝ) (hA : 0 < A) (hB : 0 < B)
    {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) :
    allOrderTailGauge A B x < allOrderTailGauge A B y := by
  have h := allOrderTailGaugeMap_strictMono A B hA hB
    (show (⟨x, hx⟩ : Set.Ici (0 : ℝ)) < ⟨y, le_trans hx hxy.le⟩ from hxy)
  change allOrderTailGauge A B x < allOrderTailGauge A B y at h
  exact h

theorem allOrderTailGauge_mono (A B : ℝ) (hA : 0 < A) (hB : 0 < B)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x ≤ y) :
    allOrderTailGauge A B x ≤ allOrderTailGauge A B y := by
  have h := (allOrderTailGaugeMap_strictMono A B hA hB).monotone
    (show (⟨x, hx⟩ : Set.Ici (0 : ℝ)) ≤ ⟨y, hy⟩ from hxy)
  change allOrderTailGauge A B x ≤ allOrderTailGauge A B y at h
  exact h

/-- Markov's inequality at a real order, retaining both coefficients of the
mixed linear/cubic growth instead of bounding either term away. -/
theorem allOrderTailMomentMarkov {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hXm : Measurable X) (hXnn : ∀ ω, 0 ≤ X ω)
    (A B : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hMom : ∀ ⦃p : ℝ⦄, 1 ≤ p →
      eLpNorm X (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (A * p + B * p ^ 3))
    (u : ℝ) (hu : 1 ≤ u) :
    μ.real {ω | allOrderTailGauge A B u < X ω} ≤ Real.exp (-u) := by
  have hu0 : 0 < u := by linarith
  let K : ℝ := A * u + B * u ^ 3
  have hK : 0 < K := by dsimp [K]; positivity
  have hthresh : 0 < allOrderTailGauge A B u := by
    unfold allOrderTailGauge
    positivity
  have hp0 : ENNReal.ofReal u ≠ 0 := by
    exact ENNReal.ofReal_ne_zero_iff.mpr hu0
  have hptop : ENNReal.ofReal u ≠ ∞ := ENNReal.ofReal_ne_top
  have hmem : MemLp X (ENNReal.ofReal u) μ := by
    apply lt_of_le_of_lt (hMom hu)
    exact ENNReal.ofReal_lt_top
  have hIntNorm : Integrable (fun ω => ‖X ω‖ ^ u) μ :=
    by simpa [ENNReal.toReal_ofReal hu0.le] using hmem.integrable_norm_rpow hp0 hptop
  have hMomK : eLpNorm X (ENNReal.ofReal u) μ ≤ ENNReal.ofReal K := by
    simpa [K] using hMom hu
  have hLp : lpNorm X (ENNReal.ofReal u) μ ≤ K := by
    calc
      lpNorm X (ENNReal.ofReal u) μ = (eLpNorm X (ENNReal.ofReal u) μ).toReal :=
        toReal_eLpNorm
      _ ≤ (ENNReal.ofReal K).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hMomK
      _ = K := ENNReal.toReal_ofReal hK.le
  have hLpEq : lpNorm X (ENNReal.ofReal u) μ =
      (∫ ω, ‖X ω‖ ^ u ∂μ) ^ u⁻¹ := by
    rw [lpNorm_eq_integral_norm_rpow_toReal hp0 hptop hXm.aestronglyMeasurable]
    simp [ENNReal.toReal_ofReal hu0.le]
  have hI0 : 0 ≤ ∫ ω, ‖X ω‖ ^ u ∂μ :=
    integral_nonneg fun ω => by positivity
  have hIbound : (∫ ω, ‖X ω‖ ^ u ∂μ) ≤ K ^ u := by
    rw [hLpEq] at hLp
    calc
      _ = ((∫ ω, ‖X ω‖ ^ u ∂μ) ^ u⁻¹) ^ u := by
        rw [Real.rpow_inv_rpow hI0 hu0.ne']
      _ ≤ K ^ u := Real.rpow_le_rpow (by positivity) hLp (by positivity)
  have hMarkov := mul_meas_ge_le_integral_of_nonneg (μ := μ)
    (f := fun ω => ‖X ω‖ ^ u)
    (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (norm_nonneg _) _)
    hIntNorm (allOrderTailGauge A B u ^ u)
  have hset : {ω | allOrderTailGauge A B u < X ω} ⊆
      {ω | allOrderTailGauge A B u ^ u ≤ ‖X ω‖ ^ u} := by
    intro ω hω
    have hpow := (Real.rpow_lt_rpow_iff hthresh.le (hXnn ω) hu0).2 hω
    simpa [Real.norm_eq_abs, abs_of_nonneg (hXnn ω)] using hpow.le
  have htail : μ.real {ω | allOrderTailGauge A B u < X ω} ≤
      K ^ u / (allOrderTailGauge A B u ^ u) := by
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hthresh u)).2
    calc
      μ.real {ω | allOrderTailGauge A B u < X ω} * allOrderTailGauge A B u ^ u =
          allOrderTailGauge A B u ^ u * μ.real {ω | allOrderTailGauge A B u < X ω} := by ring
      _ ≤ allOrderTailGauge A B u ^ u *
            μ.real {ω | allOrderTailGauge A B u ^ u ≤ ‖X ω‖ ^ u} := by
        apply mul_le_mul_of_nonneg_left
        · exact measureReal_mono (μ := μ) hset (h₂ := by finiteness)
        · exact Real.rpow_nonneg hthresh.le u
      _ ≤ ∫ ω, ‖X ω‖ ^ u ∂μ := by simpa [mul_comm] using hMarkov
      _ ≤ K ^ u := hIbound
  have hratio : K ^ u / (allOrderTailGauge A B u ^ u) = Real.exp (-u) := by
    have hmul : allOrderTailGauge A B u = Real.exp 1 * K := by
      simp [allOrderTailGauge, K]
    rw [hmul, Real.mul_rpow (le_of_lt (Real.exp_pos 1)) hK.le]
    have hexp : (Real.exp 1) ^ u = Real.exp u := by
      rw [Real.rpow_def_of_pos (Real.exp_pos 1), Real.log_exp]
      ring_nf
    rw [hexp]
    have hKpow : K ^ u ≠ 0 := (Real.rpow_pos_of_pos hK u).ne'
    field_simp [hKpow, Real.exp_ne_zero]
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  exact htail.trans_eq hratio

/-- The inverse gauge coordinate attached to a nonnegative observable. -/
noncomputable def allOrderMarkovZ {Ω : Type*} (A B : ℝ)
    (hA : 0 < A) (hB : 0 < B) (E : Ω → ℝ) : Ω → ℝ :=
  fun ω => allOrderTailInverse A B hA hB (E ω ^ 2)

/-- The Gaussian witness from the linear part of the inverse gauge. -/
noncomputable def allOrderMarkovY {Ω : Type*} (A B : ℝ)
    (hA : 0 < A) (hB : 0 < B) (E : Ω → ℝ) : Ω → ℝ :=
  fun ω => Real.sqrt (Real.exp 1 * A) *
    Real.sqrt (allOrderMarkovZ A B hA hB E ω)

/-- The stretched-exponential witness from the cubic part of the inverse gauge. -/
noncomputable def allOrderMarkovW {Ω : Type*} (A B : ℝ)
    (hA : 0 < A) (hB : 0 < B) (E : Ω → ℝ) : Ω → ℝ :=
  fun ω => Real.sqrt (Real.exp 1 * B) *
    allOrderMarkovZ A B hA hB E ω ^ (3 / 2 : ℝ)

private theorem real_rpow_three_halves_eq_mul_sqrt {x : ℝ} (hx : 0 ≤ x) :
    x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
  by_cases hx0 : x = 0
  · simp [hx0]
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  calc
    x ^ (3 / 2 : ℝ) = x ^ (1 + 1 / 2 : ℝ) := by
      congr 1
      norm_num
    _ = x ^ (1 : ℝ) * x ^ (1 / 2 : ℝ) := by
      rw [Real.rpow_add hxpos]
    _ = x * Real.sqrt x := by rw [Real.rpow_one, ← Real.sqrt_eq_rpow]

/-- Couple the inverse-gauge Markov tail into the two source weak-Orlicz
witnesses. The estimates remain reusable with any larger positive witness
scales. -/
theorem allOrderMarkovCoupled_of_moments {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (E : Ω → ℝ)
    (hEm : Measurable E) (hEnn : ∀ ω, 0 ≤ E ω)
    (A B a₁ a₂ : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hMom : ∀ ⦃p : ℝ⦄, 1 ≤ p →
      eLpNorm (fun ω => E ω ^ 2) (ENNReal.ofReal p) μ ≤
        ENNReal.ofReal (A * p + B * p ^ 3))
    (ha₁ : Real.sqrt (Real.exp 1 * A) ≤ a₁)
    (ha₂ : Real.sqrt (Real.exp 1 * B) ≤ a₂) :
    IsTwoTermBigOWithWitnesses μ (gammaSigma 2) (gammaSigma (1 / 2 : ℝ)) E
      (allOrderMarkovY A B hA hB E) (allOrderMarkovW A B hA hB E) a₁ a₂ := by
  let X : Ω → ℝ := fun ω => E ω ^ 2
  let Z : Ω → ℝ := allOrderMarkovZ A B hA hB E
  let Y : Ω → ℝ := allOrderMarkovY A B hA hB E
  let W : Ω → ℝ := allOrderMarkovW A B hA hB E
  have hXm : Measurable X := hEm.pow_const 2
  have hXnn : ∀ ω, 0 ≤ X ω := fun ω => sq_nonneg (E ω)
  have hZnn : ∀ ω, 0 ≤ Z ω := by
    intro ω
    exact allOrderTailInverse_nonneg A B hA hB (X ω)
  have hZmeas : Measurable Z := by
    exact (measurable_allOrderTailInverse A B hA hB).comp hXm
  have hZtail : IsBigOWith μ (gammaSigma 1) Z 1 := by
    rw [isBigOWith_gammaSigma_iff]
    intro t ht
    have hMarkov := allOrderTailMomentMarkov hXm hXnn A B hA hB hMom t ht
    have hEvent : upperTailEvent Z t = {ω | allOrderTailGauge A B t < X ω} := by
      ext ω
      change t < allOrderTailInverse A B hA hB (X ω) ↔
        allOrderTailGauge A B t < X ω
      constructor
      · intro htz
        have h := allOrderTailGauge_strictMono A B hA hB (le_trans zero_le_one ht) htz
        rw [allOrderTailGauge_inverse A B hA hB (X ω) (hXnn ω)] at h
        exact h
      · intro htx
        by_contra hnot
        have hzt : allOrderTailInverse A B hA hB (X ω) ≤ t := le_of_not_gt hnot
        have hmono := allOrderTailGauge_mono A B hA hB
          (allOrderTailInverse_nonneg A B hA hB (X ω)) (le_trans zero_le_one ht) hzt
        rw [allOrderTailGauge_inverse A B hA hB (X ω) (hXnn ω)] at hmono
        exact (not_lt_of_ge hmono) htx
    rw [show (1 : ℝ) * t = t by ring, Real.rpow_one, hEvent]
    exact hMarkov
  have hYroot : IsBigOWith μ (gammaSigma 2) (fun ω => Real.sqrt (Z ω)) 1 := by
    have h := (isBigOWith_gammaSigma_rpow_iff (μ := μ) (X := Z) (A := 1)
      (σ := 1) (p := (1 / 2 : ℝ)) (by norm_num) (by norm_num) hZnn).mp hZtail
    have hσ : (1 : ℝ) / (1 / 2 : ℝ) = 2 := by norm_num
    simpa [hσ, Real.sqrt_eq_rpow] using h
  have hWroot : IsBigOWith μ (gammaSigma (2 / 3 : ℝ))
      (fun ω => Z ω ^ (3 / 2 : ℝ)) 1 := by
    have h := (isBigOWith_gammaSigma_rpow_iff (μ := μ) (X := Z) (A := 1)
      (σ := 1) (p := (3 / 2 : ℝ)) (by norm_num) (by norm_num) hZnn).mp hZtail
    have hσ : (1 : ℝ) / (3 / 2 : ℝ) = 2 / 3 := by norm_num
    simpa [hσ] using h
  let c₁ : ℝ := Real.sqrt (Real.exp 1 * A)
  let c₂ : ℝ := Real.sqrt (Real.exp 1 * B)
  have hc₁ : 0 < c₁ := Real.sqrt_pos.2 (mul_pos (Real.exp_pos 1) hA)
  have hc₂ : 0 < c₂ := Real.sqrt_pos.2 (mul_pos (Real.exp_pos 1) hB)
  have hYbase : IsBigOWith μ (gammaSigma 2) Y c₁ := by
    change IsBigOWith μ (gammaSigma 2) (fun ω => c₁ * Real.sqrt (Z ω)) c₁
    simpa using (IsBigOWith.const_mul (μ := μ) (Ψ := gammaSigma 2)
        (X := fun ω => Real.sqrt (Z ω)) (A := 1) (c := c₁) hc₁.le hYroot)
  have hYtail : IsBigOWith μ (gammaSigma 2) Y a₁ := hYbase.mono_scale ha₁
  have hWbaseRaw : IsBigOWith μ (gammaSigma (2 / 3 : ℝ)) W c₂ := by
    change IsBigOWith μ (gammaSigma (2 / 3 : ℝ))
      (fun ω => c₂ * Z ω ^ (3 / 2 : ℝ)) c₂
    simpa using (IsBigOWith.const_mul (μ := μ) (Ψ := gammaSigma (2 / 3 : ℝ))
        (X := fun ω => Z ω ^ (3 / 2 : ℝ)) (A := 1) (c := c₂) hc₂.le hWroot)
  have hWbase : IsBigOWith μ (gammaSigma (1 / 2 : ℝ)) W c₂ := by
    rw [isBigOWith_gammaSigma_iff] at hWbaseRaw ⊢
    intro t ht
    have hexp : t ^ (1 / 2 : ℝ) ≤ t ^ (2 / 3 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le ht (by norm_num)
    calc
      μ.real (upperTailEvent W (c₂ * t)) ≤ Real.exp (-(t ^ (2 / 3 : ℝ))) :=
        hWbaseRaw ht
      _ ≤ Real.exp (-(t ^ (1 / 2 : ℝ))) := Real.exp_le_exp.mpr (neg_le_neg hexp)
  have hWtail : IsBigOWith μ (gammaSigma (1 / 2 : ℝ)) W a₂ := hWbase.mono_scale ha₂
  have hZpowMeas : Measurable (fun ω => Z ω ^ (3 / 2 : ℝ)) := by
    have heq : (fun ω => Z ω ^ (3 / 2 : ℝ)) = fun ω => Z ω * Real.sqrt (Z ω) := by
      funext ω
      exact real_rpow_three_halves_eq_mul_sqrt (hZnn ω)
    rw [heq]
    exact hZmeas.mul (Real.continuous_sqrt.measurable.comp hZmeas)
  have hYmeas : Measurable Y := by
    exact measurable_const.mul (Real.continuous_sqrt.measurable.comp hZmeas)
  have hWmeas : Measurable W := by
    exact measurable_const.mul hZpowMeas
  have hEbound : ∀ ω, E ω ≤ Y ω + W ω := by
    intro ω
    have hz := hZnn ω
    have hxid : X ω = allOrderTailGauge A B (Z ω) := by
      symm
      exact allOrderTailGauge_inverse A B hA hB (X ω) (hXnn ω)
    have hEeq : E ω = Real.sqrt (X ω) := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (hEnn ω)]
    have hparts :
        Real.sqrt (Real.exp 1 * (A * Z ω)) = c₁ * Real.sqrt (Z ω) ∧
        Real.sqrt (Real.exp 1 * (B * Z ω ^ 3)) = c₂ * Z ω * Real.sqrt (Z ω) := by
      constructor
      · calc
          Real.sqrt (Real.exp 1 * (A * Z ω)) =
              Real.sqrt (Real.exp 1) * Real.sqrt (A * Z ω) := by
                rw [Real.sqrt_mul (le_of_lt (Real.exp_pos 1))]
          _ = Real.sqrt (Real.exp 1) * (Real.sqrt A * Real.sqrt (Z ω)) := by
                rw [Real.sqrt_mul hA.le]
          _ = c₁ * Real.sqrt (Z ω) := by
                dsimp [c₁]
                rw [Real.sqrt_mul (le_of_lt (Real.exp_pos 1))]
                ring
      · calc
          Real.sqrt (Real.exp 1 * (B * Z ω ^ 3)) =
              Real.sqrt (Real.exp 1) * Real.sqrt (B * Z ω ^ 3) := by
                rw [Real.sqrt_mul (le_of_lt (Real.exp_pos 1))]
          _ = Real.sqrt (Real.exp 1) * (Real.sqrt B * Real.sqrt (Z ω ^ 3)) := by
                rw [Real.sqrt_mul hB.le]
          _ = c₂ * Real.sqrt (Z ω ^ 3) := by
                dsimp [c₂]
                rw [Real.sqrt_mul (le_of_lt (Real.exp_pos 1))]
                ring
          _ = c₂ * Z ω * Real.sqrt (Z ω) := by
                rw [show Z ω ^ 3 = (Z ω) ^ 2 * Z ω by ring,
                  Real.sqrt_mul (sq_nonneg (Z ω)) (Z ω), Real.sqrt_sq hz]
                ring
    have hsum :
        Real.sqrt (Real.exp 1 * (A * Z ω) + Real.exp 1 * (B * Z ω ^ 3)) ≤
          Real.sqrt (Real.exp 1 * (A * Z ω)) +
            Real.sqrt (Real.exp 1 * (B * Z ω ^ 3)) := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · have h1 := Real.sq_sqrt (mul_nonneg (le_of_lt (Real.exp_pos 1))
          (mul_nonneg hA.le hz))
        have h2 := Real.sq_sqrt (mul_nonneg (le_of_lt (Real.exp_pos 1))
          (mul_nonneg hB.le (pow_nonneg hz 3)))
        nlinarith [mul_nonneg (Real.sqrt_nonneg (Real.exp 1 * (A * Z ω)))
          (Real.sqrt_nonneg (Real.exp 1 * (B * Z ω ^ 3)))]
    calc
      E ω = Real.sqrt (X ω) := hEeq
      _ = Real.sqrt (allOrderTailGauge A B (Z ω)) := by rw [hxid]
      _ = Real.sqrt (Real.exp 1 * (A * Z ω) + Real.exp 1 * (B * Z ω ^ 3)) := by
        rw [allOrderTailGauge, mul_add]
      _ ≤ Real.sqrt (Real.exp 1 * (A * Z ω)) +
          Real.sqrt (Real.exp 1 * (B * Z ω ^ 3)) := hsum
      _ = Y ω + W ω := by
        change _ = c₁ * Real.sqrt (Z ω) + c₂ * (Z ω ^ (3 / 2 : ℝ))
        rw [hparts.1, hparts.2, real_rpow_three_halves_eq_mul_sqrt hz]
        dsimp [c₁, c₂]
        ring
  have ha₁pos : 0 < a₁ := lt_of_lt_of_le hc₁ ha₁
  have ha₂pos : 0 < a₂ := lt_of_lt_of_le hc₂ ha₂
  exact ⟨isAdmissibleTail_gammaSigma (by norm_num),
    isAdmissibleTail_gammaSigma (by norm_num), ha₁pos, ha₂pos,
    hEm, hYmeas, hWmeas, hEbound, hYtail, hWtail⟩

/-- The two witness-scale payments for the all-order history constants. -/
theorem allOrderMarkov_numeric_scales {gamma s : ℝ} (hgamma : 0 < gamma)
    (hgamma0 : gamma ≤ 17 / 50000) (hsLo : 8 * gamma ≤ s) (_hsHi : s ≤ 1) :
    Real.sqrt (Real.exp 1 * (2 ^ 29 * gamma / s ^ 2)) ≤
        2 ^ 16 * Real.sqrt gamma / s ∧
      Real.sqrt (Real.exp 1 * Real.exp (-(Real.log 2 / (1350 * gamma)))) ≤
        Real.exp (-(Real.log 2 / (8192 * gamma))) := by
  have hs : 0 < s := lt_of_lt_of_le (mul_pos (by norm_num : (0 : ℝ) < 8) hgamma) hsLo
  constructor
  · rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hroot : Real.exp 1 * (2 ^ 29 : ℝ) ≤ (2 ^ 16 : ℝ) ^ 2 := by
        exact le_of_lt ((Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2 ^ 16)).mp source_bulk_root)
      have hnum := mul_le_mul_of_nonneg_right hroot hgamma.le
      calc
        Real.exp 1 * (2 ^ 29 * gamma / s ^ 2) =
            (Real.exp 1 * (2 ^ 29 : ℝ) * gamma) / s ^ 2 := by ring
        _ ≤ ((2 ^ 16 : ℝ) ^ 2 * gamma) / s ^ 2 :=
          (div_le_div_iff_of_pos_right (sq_pos_of_pos hs)).2 hnum
        _ = (2 ^ 16 * Real.sqrt gamma / s) ^ 2 := by
          rw [div_pow, mul_pow, Real.sq_sqrt hgamma.le]
  · rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hmarginR :
          (17 / 50000 : ℝ) / 2 < (69 / 100) * (1 / 2700 - 1 / 8192) := by
        norm_num
      have hdiff : (0 : ℝ) < 1 / 2700 - 1 / 8192 := by norm_num
      have hlogCoeff :
          (69 / 100 : ℝ) * (1 / 2700 - 1 / 8192) <
            Real.log 2 * (1 / 2700 - 1 / 8192) :=
        mul_lt_mul_of_pos_right log_two_gt_69 hdiff
      have hexpCoeff : gamma <
          2 * Real.log 2 * (1 / 2700 - 1 / 8192) := by
        have hgammaHalf : gamma / 2 ≤ (17 / 50000 : ℝ) / 2 := by linarith
        have hhalf : gamma / 2 < Real.log 2 * (1 / 2700 - 1 / 8192) :=
          lt_of_le_of_lt hgammaHalf (lt_of_lt_of_le hmarginR hlogCoeff.le)
        linarith
      have hexpArg : 1 - Real.log 2 / (1350 * gamma) ≤
          -(Real.log 2 / (8192 * gamma)) * 2 := by
        field_simp [hgamma.ne']
        nlinarith [hexpCoeff]
      calc
        Real.exp 1 * Real.exp (-(Real.log 2 / (1350 * gamma))) =
            Real.exp (1 - Real.log 2 / (1350 * gamma)) := by
              rw [← Real.exp_add]
              congr 1
        _ ≤ Real.exp (-(Real.log 2 / (8192 * gamma)) * 2) :=
          Real.exp_le_exp.mpr hexpArg
        _ = Real.exp (-(Real.log 2 / (8192 * gamma))) ^ 2 := by
          rw [pow_two, ← Real.exp_add]
          congr 1
          ring

/-- AO-MARKOV-COUPLED with its sole predecessor input in exact source form:
the internal 1350-rate all-order moment bound. -/
theorem allOrderMarkovCoupled_of_history (M : ABKModel 2) (m : ℤ) (s : ℝ)
    (hs : s ∈ Set.Icc (8 * M.gamma) 1) (hgamma : M.gamma ≤ 17 / 50000)
    (hMom : ∀ ⦃p : ℝ⦄, 1 ≤ p →
      eLpNorm
          (fun ω => Observable.cutoffHomogenizationError M m
            ⟨s, (mul_pos (by norm_num : (0 : ℝ) < 8) M.shellPrefix.gamma_pos).trans_le hs.1⟩ ω ^ 2)
          (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure ≤
        ENNReal.ofReal
          (2 ^ 29 * M.gamma * p / s ^ 2 +
            Real.exp (-(Real.log 2 / (1350 * M.gamma))) * p ^ 3)) :
    Probability.IsTwoTermBigOWith (Cutoff.cutoffSampleLaw M).toMeasure
      (gammaSigma 2) (gammaSigma (1 / 2 : ℝ))
      (Observable.cutoffHomogenizationError M m
        ⟨s, (mul_pos (by norm_num : (0 : ℝ) < 8) M.shellPrefix.gamma_pos).trans_le hs.1⟩)
      (2 ^ 16 * Real.sqrt M.gamma / s)
      (Real.exp (-(Real.log 2 / (8192 * M.gamma)))) := by
  let sPos : {s : ℝ // 0 < s} :=
    ⟨s, (mul_pos (by norm_num : (0 : ℝ) < 8) M.shellPrefix.gamma_pos).trans_le hs.1⟩
  let E : Cutoff.CutoffSample 2 → ℝ :=
    Observable.cutoffHomogenizationError M m sPos
  let A : ℝ := 2 ^ 29 * M.gamma / s ^ 2
  let B : ℝ := Real.exp (-(Real.log 2 / (1350 * M.gamma)))
  have hgammaPos : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hsPos : 0 < s := sPos.2
  have hEm : Measurable E := by
    exact Observable.measurable_cutoffHomogenizationError M m sPos
  have hEnn : ∀ ω, 0 ≤ E ω := by
    intro ω
    exact Observable.cutoffHomogenizationError_nonneg M m sPos ω
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hMomAB : ∀ ⦃p : ℝ⦄, 1 ≤ p →
      eLpNorm (fun ω => E ω ^ 2) (ENNReal.ofReal p)
          (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (A * p + B * p ^ 3) := by
    intro p hp
    have h := hMom hp
    have hEq : A * p + B * p ^ 3 =
        2 ^ 29 * M.gamma * p / s ^ 2 +
          Real.exp (-(Real.log 2 / (1350 * M.gamma))) * p ^ 3 := by
      dsimp [A, B]
      ring
    rw [hEq]
    exact h
  have hsc := allOrderMarkov_numeric_scales hgammaPos hgamma hs.1 hs.2
  have ha₁ : Real.sqrt (Real.exp 1 * A) ≤ 2 ^ 16 * Real.sqrt M.gamma / s := by
    simpa [A] using hsc.1
  have ha₂ : Real.sqrt (Real.exp 1 * B) ≤
      Real.exp (-(Real.log 2 / (8192 * M.gamma))) := by
    simpa [B] using hsc.2
  have hWitness := allOrderMarkovCoupled_of_moments E hEm hEnn A B
    (2 ^ 16 * Real.sqrt M.gamma / s)
    (Real.exp (-(Real.log 2 / (8192 * M.gamma)))) hA hB hMomAB ha₁ ha₂
  exact ⟨allOrderMarkovY A B hA hB E, allOrderMarkovW A B hA hB E, hWitness⟩

end ASDExplicitGamma.AllOrder

