/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Gaussian.P12Regularized
public import ASDExplicitGamma.AllOrder.CirGenerator19
public import ASDExplicitGamma.Numerics.AllOrder.CirGates

/-! # CIR all-real-order moment transport -/

@[expose] public section

open Homogenization Algsuperdiff.Section3 MeasureTheory Set
open Filter
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Model
  ASDExplicitGamma.Response ASDExplicitGamma.Triadic
open scoped ENNReal Topology

namespace ASDExplicitGamma.AllOrder

/-- Apply GA-P12 to a path whose pointwise generator and common-coordinate
carré-du-champ obey the CIR adapters.  The first component retains the
regularized `1<p<2` differential assertion; the second is the integrated
all-real-order transport.  The final component records the exact coefficient
allocations consumed by the finite-even induction. -/
theorem aoCir_moment_transport_of_pathwise_bounds {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y G Γ L : ℝ → Ω → ℝ) {p vbar : ℝ} (hp : 1 ≤ p)
    (hvbar : 0 ≤ vbar) (hY0 : ∀ t ω, 0 ≤ Y t ω) (hL0 : ∀ t ω, 0 ≤ L t ω)
    (hYmem : ∀ q, 1 < q → ∀ t, MemLp (Y t) (ENNReal.ofReal q) μ)
    (hLmem : ∀ q, 1 ≤ q → ∀ t, MemLp (L t) (ENNReal.ofReal q) μ)
    (hdata : ∀ q, 1 < q → ∀ ε, 0 < ε →
      ASDExplicitGamma.Gaussian.P12RegularizedHeatData μ Y G Γ q ε)
    (hgen : ∀ t ω, G t ω ≤ 19 * vbar * L t ω)
    (hbracket : ∀ t ω, Γ t ω ≤ 16 * vbar * Y t ω * L t ω)
    (hFcont1 : ContinuousOn (fun t => ∫ ω, Y t ω ∂μ) (Icc 0 1))
    (hheat1 : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun r => ∫ ω, Y r ω ∂μ) (∫ ω, G t ω ∂μ) t)
    (hGint : ∀ t ∈ Ioo (0 : ℝ) 1, Integrable (G t) μ)
    (hU : IntegrableOn (fun t => (19 + 8 * (p - 1)) * vbar *
      ASDExplicitGamma.Gaussian.positiveLpNorm μ p (L t)) (Icc 0 1)) :
    ((1 < p ∧ p < 2) → ∀ ε, 0 < ε →
      ∀ t ∈ Ioo (0 : ℝ) 1,
        deriv (fun r => (∫ ω, (Y r ω + ε) ^ p ∂μ) ^ p⁻¹) t ≤
          (19 + 8 * (p - 1)) * vbar *
            ASDExplicitGamma.Gaussian.positiveLpNorm μ p (L t)) ∧
    ((s t : ℝ) → 0 ≤ s → s ≤ t → t ≤ 1 →
      ASDExplicitGamma.Gaussian.positiveLpNorm μ p (Y t) -
        ASDExplicitGamma.Gaussian.positiveLpNorm μ p (Y s) ≤
          ∫ r in s..t, (19 + 8 * (p - 1)) * vbar *
            ASDExplicitGamma.Gaussian.positiveLpNorm μ p (L r)) ∧
    ((1 ≤ p → 19 + 8 * (p - 1) ≤ 19 * p) ∧
      (12 ≤ p → 19 + 8 * (p - 1) ≤ (107 / 12) * p)) := by
  have htransport := ASDExplicitGamma.Gaussian.p12_all_order_heat_transport
    μ Y G Γ L hp hvbar hY0 hL0 hYmem hLmem hdata hgen hbracket
    hFcont1 hheat1 hGint hU
  have halloc := ASDExplicitGamma.Numerics.AllOrder.cir_order_allocations p
  refine ⟨htransport.1, htransport.2, ?_⟩
  exact ⟨fun hp' => halloc.2 hp', fun hp12 => halloc.1 hp12⟩

/-- Extend a heat path by zero off its natural insertion interval.  This keeps
the global MemLp API of the generic transport theorem while asking the actual
model only for moments on the interval where its inserted coefficient is
elliptic. -/
private noncomputable def aoCirUnitIntervalExtend {Ω : Type*} (f : ℝ → Ω → ℝ) :
    ℝ → Ω → ℝ := fun t ω => if t ∈ Icc (0 : ℝ) 1 then f t ω else 0

/-- P12 transport with its stochastic and pathwise inputs restricted to the
actual unit heat interval.  The zero extension is purely an adapter for the
generic theorem: every conclusion is returned on `[0,1]` for the original
paths. -/
theorem aoCir_moment_transport_of_pathwise_bounds_on_unit_interval
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y G Γ L : ℝ → Ω → ℝ) {p vbar : ℝ} (hp : 1 ≤ p)
    (hvbar : 0 ≤ vbar) (hY0 : ∀ t ω, 0 ≤ Y t ω) (hL0 : ∀ t ω, 0 ≤ L t ω)
    (hYmem : ∀ q, 1 < q → ∀ t ∈ Icc (0 : ℝ) 1,
      MemLp (Y t) (ENNReal.ofReal q) μ)
    (hLmem : ∀ q, 1 ≤ q → ∀ t ∈ Icc (0 : ℝ) 1,
      MemLp (L t) (ENNReal.ofReal q) μ)
    (hdata : ∀ q, 1 < q → ∀ ε, 0 < ε →
      ASDExplicitGamma.Gaussian.P12RegularizedHeatData μ Y G Γ q ε)
    (hgen : ∀ t ∈ Icc (0 : ℝ) 1, ∀ ω, G t ω ≤ 19 * vbar * L t ω)
    (hbracket : ∀ t ∈ Icc (0 : ℝ) 1, ∀ ω,
      Γ t ω ≤ 16 * vbar * Y t ω * L t ω)
    (hFcont1 : ContinuousOn (fun t => ∫ ω, Y t ω ∂μ) (Icc 0 1))
    (hheat1 : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun r => ∫ ω, Y r ω ∂μ) (∫ ω, G t ω ∂μ) t)
    (hU : IntegrableOn (fun t => (19 + 8 * (p - 1)) * vbar *
      ASDExplicitGamma.Gaussian.positiveLpNorm μ p (L t)) (Icc 0 1)) :
    ((s t : ℝ) → 0 ≤ s → s ≤ t → t ≤ 1 →
      ASDExplicitGamma.Gaussian.positiveLpNorm μ p (Y t) -
        ASDExplicitGamma.Gaussian.positiveLpNorm μ p (Y s) ≤
          ∫ r in s..t, (19 + 8 * (p - 1)) * vbar *
            ASDExplicitGamma.Gaussian.positiveLpNorm μ p (L r)) := by
  classical
  let Ye := aoCirUnitIntervalExtend Y
  let Ge := aoCirUnitIntervalExtend G
  let Γe := aoCirUnitIntervalExtend Γ
  let Le := aoCirUnitIntervalExtend L
  have hYe0 : ∀ t ω, 0 ≤ Ye t ω := by
    intro t ω
    by_cases ht : t ∈ Icc (0 : ℝ) 1
    · simp [Ye, aoCirUnitIntervalExtend, ht, hY0]
    · simp [Ye, aoCirUnitIntervalExtend, ht]
  have hLe0 : ∀ t ω, 0 ≤ Le t ω := by
    intro t ω
    by_cases ht : t ∈ Icc (0 : ℝ) 1
    · simp [Le, aoCirUnitIntervalExtend, ht, hL0]
    · simp [Le, aoCirUnitIntervalExtend, ht]
  have hYmem' : ∀ q, 1 < q → ∀ t,
      MemLp (Ye t) (ENNReal.ofReal q) μ := by
    intro q hq t
    by_cases ht : t ∈ Icc (0 : ℝ) 1
    · have hEq : Ye t = Y t := by
        funext ω
        simp [Ye, aoCirUnitIntervalExtend, ht]
      simpa only [hEq] using hYmem q hq t ht
    · have hEq : Ye t = fun _ : Ω => (0 : ℝ) := by
        funext ω
        simp [Ye, aoCirUnitIntervalExtend, ht]
      rw [hEq]
      exact memLp_const (0 : ℝ)
  have hLmem' : ∀ q, 1 ≤ q → ∀ t,
      MemLp (Le t) (ENNReal.ofReal q) μ := by
    intro q hq t
    by_cases ht : t ∈ Icc (0 : ℝ) 1
    · have hEq : Le t = L t := by
        funext ω
        simp [Le, aoCirUnitIntervalExtend, ht]
      simpa only [hEq] using hLmem q hq t ht
    · have hEq : Le t = fun _ : Ω => (0 : ℝ) := by
        funext ω
        simp [Le, aoCirUnitIntervalExtend, ht]
      rw [hEq]
      exact memLp_const (0 : ℝ)
  have hdata' : ∀ q, 1 < q → ∀ ε, 0 < ε →
      ASDExplicitGamma.Gaussian.P12RegularizedHeatData μ Ye Ge Γe q ε := by
    intro q hq ε hε
    let D := hdata q hq ε hε
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine D.moment_continuous.congr ?_
      intro t ht
      simp [Ye, aoCirUnitIntervalExtend, ht]
    · intro t ht
      simpa [Ye, aoCirUnitIntervalExtend, ht] using D.moment_positive t ht
    · intro t ht
      let F₀ : ℝ → ℝ := fun r => ∫ ω, (Y r ω + ε) ^ q ∂μ
      let F₁ : ℝ → ℝ := fun r => ∫ ω, (Ye r ω + ε) ^ q ∂μ
      have hevent : F₁ =ᶠ[𝓝 t] F₀ := by
        filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
        have hEq : Ye r = Y r := by
          funext ω
          simp [Ye, aoCirUnitIntervalExtend, Set.mem_Icc.mpr ⟨hr.1.le, hr.2.le⟩]
        simp only [F₀, F₁, hEq]
      have hder := (D.heat_derivative t ht).congr_of_eventuallyEq hevent
      have hEqY : Ye t = Y t := by
        funext ω
        simp [Ye, aoCirUnitIntervalExtend, Set.mem_Icc.mpr ⟨ht.1.le, ht.2.le⟩]
      rw [← hEqY] at hder
      simpa [F₁, Ge, Γe, aoCirUnitIntervalExtend, Set.mem_Icc.mpr ⟨ht.1.le, ht.2.le⟩]
        using hder
    · intro t ht
      have hEqY : Ye t = Y t := by
        funext ω
        simp [Ye, aoCirUnitIntervalExtend, Set.mem_Icc.mpr ⟨ht.1.le, ht.2.le⟩]
      have hEqG : Ge t = G t := by
        funext ω
        simp [Ge, aoCirUnitIntervalExtend, Set.mem_Icc.mpr ⟨ht.1.le, ht.2.le⟩]
      have hEqΓ : Γe t = Γ t := by
        funext ω
        simp [Γe, aoCirUnitIntervalExtend, Set.mem_Icc.mpr ⟨ht.1.le, ht.2.le⟩]
      simpa only [hEqY, hEqG, hEqΓ] using D.heat_integrable t ht
  have hgen' : ∀ t ω, Ge t ω ≤ 19 * vbar * Le t ω := by
    intro t ω
    by_cases ht : t ∈ Icc (0 : ℝ) 1
    · simpa [Ge, Le, aoCirUnitIntervalExtend, ht] using hgen t ht ω
    · simp [Ge, Le, aoCirUnitIntervalExtend, ht]
  have hbracket' : ∀ t ω, Γe t ω ≤ 16 * vbar * Ye t ω * Le t ω := by
    intro t ω
    by_cases ht : t ∈ Icc (0 : ℝ) 1
    · simpa [Γe, Ye, Le, aoCirUnitIntervalExtend, ht] using hbracket t ht ω
    · simp [Γe, Ye, Le, aoCirUnitIntervalExtend, ht]
  have hFcont' : ContinuousOn (fun t => ∫ ω, Ye t ω ∂μ) (Icc 0 1) := by
    refine hFcont1.congr ?_
    intro t ht
    have hEq : Ye t = Y t := by
      funext ω
      simp [Ye, aoCirUnitIntervalExtend, ht]
    simp only [hEq]
  have hheat' : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun r => ∫ ω, Ye r ω ∂μ) (∫ ω, Ge t ω ∂μ) t := by
    intro t ht
    have hevent : (fun r => ∫ ω, Ye r ω ∂μ) =ᶠ[𝓝 t]
        (fun r => ∫ ω, Y r ω ∂μ) := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
      have hEq : Ye r = Y r := by
        funext ω
        simp [Ye, aoCirUnitIntervalExtend, Set.mem_Icc.mpr ⟨hr.1.le, hr.2.le⟩]
      simp only [hEq]
    have hder := (hheat1 t ht).congr_of_eventuallyEq hevent
    have hEqG : Ge t = G t := by
      funext ω
      simp [Ge, aoCirUnitIntervalExtend, Set.mem_Icc.mpr ⟨ht.1.le, ht.2.le⟩]
    simpa only [hEqG] using hder
  have hU' : IntegrableOn (fun t => (19 + 8 * (p - 1)) * vbar *
      ASDExplicitGamma.Gaussian.positiveLpNorm μ p (Le t)) (Icc 0 1) := by
    apply hU.congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have hEq : Le t = L t := by
      funext ω
      simp [Le, aoCirUnitIntervalExtend, ht]
    simp only [hEq]
  have hgenInt : ∀ t ∈ Ioo (0 : ℝ) 1, Integrable (Ge t) μ := by
    intro t ht
    let D₁ := hdata 2 (by norm_num) 1 (by norm_num)
    let D₂ := hdata 2 (by norm_num) 2 (by norm_num)
    have h₁ := D₁.heat_integrable t ht
    have h₂ := D₂.heat_integrable t ht
    have h₁' : Integrable (fun ω => 2 * (Y t ω + 1) * G t ω + Γ t ω) μ := by
      simpa [show (2 : ℝ) - 1 = 1 by norm_num,
        show (2 : ℝ) - 2 = 0 by norm_num,
        Real.rpow_one, Real.rpow_zero] using h₁
    have h₂' : Integrable (fun ω => 2 * (Y t ω + 2) * G t ω + Γ t ω) μ := by
      simpa [show (2 : ℝ) - 1 = 1 by norm_num,
        show (2 : ℝ) - 2 = 0 by norm_num,
        Real.rpow_one, Real.rpow_zero] using h₂
    have hdiff : (fun ω => 2 * (Y t ω + 2) * G t ω + Γ t ω) -
        (fun ω => 2 * (Y t ω + 1) * G t ω + Γ t ω) = fun ω => 2 * G t ω := by
      funext ω
      change (2 * (Y t ω + 2) * G t ω + Γ t ω) -
        (2 * (Y t ω + 1) * G t ω + Γ t ω) = 2 * G t ω
      ring_nf
    have hGtwo : Integrable (fun ω => 2 * G t ω) μ := by
      rw [← hdiff]
      exact h₂'.sub h₁'
    have hG : Integrable (G t) μ := by
      convert hGtwo.const_mul (1 / 2 : ℝ) using 1
      ext ω
      ring
    have hEqGe : Ge t = G t := by
      funext ω
      simp [Ge, aoCirUnitIntervalExtend, Set.mem_Icc.mpr ⟨ht.1.le, ht.2.le⟩]
    simpa only [hEqGe] using hG
  have htransport := aoCir_moment_transport_of_pathwise_bounds μ Ye Ge Γe Le hp
    hvbar hYe0 hLe0 hYmem' hLmem' hdata' hgen' hbracket' hFcont' hheat'
    hgenInt hU'
  intro s t hs hst ht
  have hmain := htransport.2.1 s t hs hst ht
  have hEqY0 : Ye s = Y s := by
    funext ω
    simp [Ye, aoCirUnitIntervalExtend, Set.mem_Icc.mpr ⟨hs, le_trans hst ht⟩]
  have hEqY1 : Ye t = Y t := by
    funext ω
    simp [Ye, aoCirUnitIntervalExtend, Set.mem_Icc.mpr ⟨le_trans hs hst, ht⟩]
  have hRange : ∀ r ∈ Set.uIcc s t, r ∈ Icc (0 : ℝ) 1 := by
    intro r hr
    rw [Set.uIcc_of_le hst] at hr
    exact ⟨le_trans hs hr.1, le_trans hr.2 ht⟩
  have hEqL : ∀ r ∈ Set.uIcc s t, Le r = L r := by
    intro r hr
    have hrI : r ∈ Icc (0 : ℝ) 1 := hRange r hr
    funext ω
    simp [Le, aoCirUnitIntervalExtend, hrI]
  have hintEq : (∫ r in s..t, (19 + 8 * (p - 1)) * vbar *
        ASDExplicitGamma.Gaussian.positiveLpNorm μ p (Le r)) =
      ∫ r in s..t, (19 + 8 * (p - 1)) * vbar *
        ASDExplicitGamma.Gaussian.positiveLpNorm μ p (L r) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with r hr
    have hrIcc : r ∈ Set.uIcc s t := by
      rw [Set.uIcc_of_le hst]
      rw [Set.uIoc_of_le hst] at hr
      exact ⟨hr.1.le, hr.2⟩
    rw [hEqL r hrIcc]
  simpa only [hEqY0, hEqY1, hintEq] using hmain

end ASDExplicitGamma.AllOrder
