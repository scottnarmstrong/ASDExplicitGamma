/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.AllOrder.ProfileCaps
public import ASDExplicitGamma.AllOrder.CirFiniteEven
public import ASDExplicitGamma.Inverse.OrderResetInterface

/-! # Source all-order profile adapter and finite-even profile caps -/

@[expose] public section

open Homogenization MeasureTheory Algsuperdiff.Section3
open scoped ENNReal

namespace ASDExplicitGamma.AllOrder

/-- Exact real-valued conclusion of the order-reset producer.
It is named separately here so the AO-ALL-PROFILE adapter can be stated independently
of the producer theorem. -/
def orderResetProfileConclusion (M : ABKModel 2) (Q : TriadicCube 2)
    (p : ℝ) (N K₀ : ℤ) (weights : ℤ → ℝ) : Prop :=
  let m := Inverse.protectedOldLabel Q.scale (Inverse.orderBand p)
  let D := ((N - Q.scale + 1 : ℤ) : ℝ)
  let f := |((K₀ - Q.scale + 1 : ℤ) : ℝ)|
  eLpNorm (Inverse.rootTraceObservable M Q m N K₀ weights) (ENNReal.ofReal p)
      (Cutoff.cutoffSampleLaw M).toMeasure ≤
    ENNReal.ofReal (Inverse.orderTraceProfile M.gamma p D f) ∧
  eLpNorm (Inverse.rootInverseObservable M Q m N K₀ weights) (ENNReal.ofReal p)
      (Cutoff.cutoffSampleLaw M).toMeasure ≤
    ENNReal.ofReal (Inverse.orderInverseProfile (207 / 100) M.gamma p f) ∧
  (M.gamma ≤ 1 / 327680 →
    eLpNorm (Inverse.rootInverseObservable M Q m N K₀ weights)
        (ENNReal.ofReal p) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (Inverse.orderInverseProfile (153 / 100) M.gamma p f))

/-- A producer with the exact order-reset statement. -/
abbrev OrderResetProducer : Prop :=
  ∀ (M : ABKModel 2) (h : ℝ)
    (_hM : PlanarQ3Gaussian M h) (_hγ : M.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (p : ℝ) (_hp : 2 ≤ p)
    (_hpast : ∀ n : ℤ,
      n ≤ Q.scale - 342 - 12 * Inverse.orderBand p → nativeInductionState M h n)
    (N K₀ : ℤ) (_hN : Q.scale - 1 ≤ N) (weights : ℤ → ℝ)
    (_hw : ∀ n ∈ Finset.Ioc
      (Inverse.protectedOldLabel Q.scale (Inverse.orderBand p)) N,
      0 ≤ weights n ∧ weights n ≤ 1),
    orderResetProfileConclusion M Q p N K₀ weights

/-- Conditional AO-ALL-PROFILE adapter. Its only dependency is the stable,
exactly typed order-reset producer above; the order-reset theorem instantiates this
helper. -/
theorem ao_all_profile_of_order_reset
    (reset : OrderResetProducer)
    (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (hγ : M.gamma ≤ gammaZero)
    (Q : TriadicCube 2) (p : ℝ) (hp : 2 ≤ p)
    (hpast : ∀ n : ℤ,
      n ≤ Q.scale - 342 - 12 * Inverse.orderBand p → nativeInductionState M h n)
    (N K₀ : ℤ) (hN : Q.scale - 1 ≤ N) (weights : ℤ → ℝ)
    (hw : ∀ n ∈ Finset.Ioc
      (Inverse.protectedOldLabel Q.scale (Inverse.orderBand p)) N,
      0 ≤ weights n ∧ weights n ≤ 1) :
    orderResetProfileConclusion M Q p N K₀ weights := by
  exact reset M h hM hγ Q p hp hpast N K₀ hN weights hw

/-- The two numerical CIR caps follow from the literal profiles over
the small-gamma staircase band. The inputs `htrace` and `hinverse` are exactly
the corresponding profile conclusions, not cap assumptions. -/
theorem aoCir_small_gamma_caps_of_all_profile
    {γ qT qI D fT fI : ℝ} {T I : ℝ≥0∞}
    (hγ : 0 < γ) (hγsmall : γ ≤ 1 / 327680)
    (hqT : 2 ≤ qT) (hqTband : qT ≤ 4 * (smallGammaSeedP γ : ℝ))
    (hqI : 48 ≤ qI) (hqIband : qI ≤ 4 * (smallGammaSeedP γ : ℝ))
    (hD0 : 0 ≤ D) (hD : D ≤ 9)
    (hfT0 : 0 ≤ fT) (hfT : fT ≤ 1)
    (hfI0 : 0 ≤ fI) (hfI : fI ≤ 5)
    (htrace : T ≤ ENNReal.ofReal (Inverse.orderTraceProfile γ qT D fT))
    (hinverse : I ≤ ENNReal.ofReal
      (Inverse.orderInverseProfile (153 / 100) γ qI fI)) :
    T ≤ ENNReal.ofReal 50 ∧
      aoCirInverseHistoryFactor γ * (3 : ℝ) ^ (8 / qI) * I.toReal < 2.2 := by
  have hγpos : 0 ≤ γ := hγ.le
  have hbandT := aoCir_small_gamma_profile_band_bounds hγ hγsmall hqT hqTband
  have hqI2 : 2 ≤ qI := by linarith
  have hbandI := aoCir_small_gamma_profile_band_bounds hγ hγsmall hqI2 hqIband
  let hT : ℝ := (Inverse.heightEntrance (Inverse.orderBand qT) : ℝ)
  let hI : ℝ := (Inverse.heightEntrance (Inverse.orderBand qI) : ℝ)
  have hTnonneg : 0 ≤ hT := by dsimp [hT]; positivity
  have hInonneg : 0 ≤ hI := by dsimp [hI]; positivity
  have hqTnonneg : 0 ≤ qT := by linarith
  have htraceReal :
      Inverse.orderTraceProfile γ qT D fT ≤
        4 * (2 + 2810 * γ * (hT + 20 + qT * (D + 1))) *
          (3 : ℝ) ^ (4 * γ * (hT + 20) + 2 * γ * D + 2 * γ * fT) := by
    rfl
  have htraceCap := aoCir_small_gamma_trace_profile_cap
    (γ := γ) (h := hT) (p := qT) (D := D) (f := fT)
    (T := Inverse.orderTraceProfile γ qT D fT)
    hγpos hTnonneg hγsmall hqTnonneg hD0 hD hfT0 hfT hbandT.1.le hbandT.2
    htraceReal
  have hinverseReal :
      Inverse.orderInverseProfile (153 / 100) γ qI fI ≤
        (153 / 100 : ℝ) *
          (3 : ℝ) ^ (2 * γ * (hI + 20) + 2 * γ * fI) := by
    rfl
  have hinverseCap := aoCir_small_gamma_inverse_profile_cap
    (γ := γ) (h := hI) (f := fI) (q := qI)
    (R := Inverse.orderInverseProfile (153 / 100) γ qI fI)
    hγpos hInonneg hγsmall hbandI.1.le hfI0 hfI hqI hinverseReal
  have htraceCapENN : T ≤ ENNReal.ofReal 50 :=
    htrace.trans (ENNReal.ofReal_le_ofReal htraceCap.le)
  have hinverseRealNonneg :
      0 ≤ Inverse.orderInverseProfile (153 / 100) γ qI fI := by
    unfold Inverse.orderInverseProfile
    positivity
  have hIreal : I.toReal ≤ Inverse.orderInverseProfile (153 / 100) γ qI fI := by
    calc
      I.toReal ≤ (ENNReal.ofReal
          (Inverse.orderInverseProfile (153 / 100) γ qI fI)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hinverse
      _ = Inverse.orderInverseProfile (153 / 100) γ qI fI :=
        ENNReal.toReal_ofReal hinverseRealNonneg
  have hfactorNonneg : 0 ≤ aoCirInverseHistoryFactor γ * (3 : ℝ) ^ (8 / qI) := by
    have hγupper : γ ≤ 17 / 50000 := by norm_num at hγsmall ⊢; linarith
    exact mul_nonneg (aoCir_inverse_history_factor_cap hγupper).1
      (Real.rpow_nonneg (by norm_num) _)
  refine ⟨htraceCapENN, ?_⟩
  calc
    aoCirInverseHistoryFactor γ * (3 : ℝ) ^ (8 / qI) * I.toReal ≤
        aoCirInverseHistoryFactor γ * (3 : ℝ) ^ (8 / qI) *
          Inverse.orderInverseProfile (153 / 100) γ qI fI :=
      mul_le_mul_of_nonneg_left hIreal hfactorNonneg
    _ < 2.2 := hinverseCap

end ASDExplicitGamma.AllOrder
