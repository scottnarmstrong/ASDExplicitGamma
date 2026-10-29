module

public import ASDExplicitGamma.Inverse.ParentGapHolder
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-! The correlated local-history moment from the global inverse split. -/

@[expose] public section

namespace ASDExplicitGamma.Inverse

open MeasureTheory
open scoped ENNReal

/-- A source-energy bound for the local first-corrector square and the
pathwise weak-history control combine with the positive global split to give
the correlated `B* V_l²` moment. The remainder uses the mixed L¹²⁸/L² Holder
bound, keeping the OLD source energy and NEW bank constants separate. -/
theorem mixed_bridge_local_history_moment
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (B R H V : Ω → ℝ) (β ε D ξ Hcap : ℝ)
    (hβ : 0 ≤ β) (hε : 0 ≤ ε) (hD : 0 ≤ D) (hξ : 0 ≤ ξ) (hHcap : 0 ≤ Hcap)
    (hB0 : ∀ ω, 0 ≤ B ω) (hR0 : ∀ ω, 0 ≤ R ω) (hH0 : ∀ ω, 0 ≤ H ω)
    (hBmeas : AEStronglyMeasurable B μ) (hRmeas : AEStronglyMeasurable R μ)
    (hHmeas : AEStronglyMeasurable H μ) (hVmeas : AEStronglyMeasurable V μ)
    (hSplit : ∀ ω, B ω ≤ β + R ω)
    (hB128 : eLpNorm B 128 μ ≤ ENNReal.ofReal β)
    (hR128 : eLpNorm R 128 μ ≤ ENNReal.ofReal ε)
    (hH2 : eLpNorm H 2 μ ≤ ENNReal.ofReal Hcap)
    (hVsource : ∫⁻ ω, ENNReal.ofReal (V ω ^ 2) ∂μ ≤ ENNReal.ofReal ξ)
    (hVweak : ∀ ω, V ω ^ 2 ≤ D * B ω * H ω) :
    ∫⁻ ω, ENNReal.ofReal (B ω * V ω ^ 2) ∂μ ≤
      ENNReal.ofReal (β * ξ + ε * D * β * Hcap) := by
  let P : Fin 4 → Ω → ℝ := fun i ω =>
    if i = 0 then R ω else if i = 1 then B ω else 1
  let E : Fin 4 → ℝ := fun i => if i = 0 then ε else if i = 1 then β else 1
  have hconst : eLpNorm (fun _ : Ω => (1 : ℝ)) 128 μ = 1 := by
    rw [eLpNorm_const' (1 : ℝ) (by norm_num) (by norm_num),
      Real.enorm_of_nonneg (by norm_num : 0 ≤ (1 : ℝ))]
    simp only [measure_univ, ENNReal.one_rpow, mul_one]
    norm_num
  have hP0 (i : Fin 4) (ω : Ω) : 0 ≤ P i ω := by
    by_cases hi0 : i = 0
    · simp [P, hi0, hR0 ω]
    · by_cases hi1 : i = 1
      · simp [P, hi1, hB0 ω]
      · simp [P, hi0, hi1]
  have hPmeas (i : Fin 4) : AEStronglyMeasurable (P i) μ := by
    by_cases hi0 : i = 0
    · simpa [P, hi0] using hRmeas
    · by_cases hi1 : i = 1
      · simpa [P, hi0, hi1] using hBmeas
      · simpa [P, hi0, hi1] using
          (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : Ω => (1 : ℝ)) μ)
  have hP128 (i : Fin 4) : eLpNorm (P i) 128 μ ≤ ENNReal.ofReal (E i) := by
    by_cases hi0 : i = 0
    · simpa [P, E, hi0] using hR128
    · by_cases hi1 : i = 1
      · simpa [P, E, hi0, hi1] using hB128
      · simpa [P, E, hi0, hi1] using (le_of_eq hconst)
  have hholder := parent_gap_four_rare_trace_holder P H E Hcap
    hP0 hH0 hPmeas hHmeas hP128 hH2
  have hPprod (ω : Ω) :
      ∏ i : Fin 4, ENNReal.ofReal (P i ω) =
        ENNReal.ofReal (R ω) * ENNReal.ofReal (B ω) := by
    norm_num [P, Fin.prod_univ_succ]
  have hEprod : ∏ i : Fin 4, ENNReal.ofReal (E i) =
      ENNReal.ofReal ε * ENNReal.ofReal β := by
    norm_num [E, Fin.prod_univ_succ]
  have hRBH :
      ∫⁻ ω, ENNReal.ofReal (R ω) * ENNReal.ofReal (B ω) *
        ENNReal.ofReal (H ω) ∂μ ≤
      ENNReal.ofReal Hcap * (ENNReal.ofReal ε * ENNReal.ofReal β) := by
    calc
      _ = ∫⁻ ω, (∏ i : Fin 4, ENNReal.ofReal (P i ω)) *
          ENNReal.ofReal (H ω) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards with ω
        rw [hPprod ω]
      _ ≤ ENNReal.ofReal Hcap * ∏ i : Fin 4, ENNReal.ofReal (E i) := hholder
      _ = _ := by rw [hEprod]
  have hV2meas : AEMeasurable (fun ω => ENNReal.ofReal (V ω ^ 2)) μ :=
    ENNReal.continuous_ofReal.measurable.comp_aemeasurable
      (hVmeas.aemeasurable.pow_const 2)
  have hbaseMeas : AEMeasurable
      (fun ω => ENNReal.ofReal β * ENNReal.ofReal (V ω ^ 2)) μ :=
    hV2meas.const_mul _
  have hpoint (ω : Ω) :
      ENNReal.ofReal (B ω * V ω ^ 2) ≤
        ENNReal.ofReal β * ENNReal.ofReal (V ω ^ 2) +
          ENNReal.ofReal D *
            (ENNReal.ofReal (R ω) * ENNReal.ofReal (B ω) * ENNReal.ofReal (H ω)) := by
    have hVweak' : V ω ^ 2 ≤ D * (B ω * H ω) := by nlinarith [hVweak ω]
    have hreal : B ω * V ω ^ 2 ≤ β * V ω ^ 2 + D * (R ω * (B ω * H ω)) := by
      calc
        B ω * V ω ^ 2 ≤ (β + R ω) * V ω ^ 2 :=
          mul_le_mul_of_nonneg_right (hSplit ω) (sq_nonneg (V ω))
        _ = β * V ω ^ 2 + R ω * V ω ^ 2 := by ring
        _ ≤ β * V ω ^ 2 + R ω * (D * (B ω * H ω)) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hVweak' (hR0 ω))
        _ = β * V ω ^ 2 + D * (R ω * (B ω * H ω)) := by ring
    have hβV : 0 ≤ β * V ω ^ 2 := mul_nonneg hβ (sq_nonneg _)
    have hBH0 : 0 ≤ B ω * H ω := mul_nonneg (hB0 ω) (hH0 ω)
    have hRBH0 : 0 ≤ R ω * (B ω * H ω) := mul_nonneg (hR0 ω) hBH0
    have hDRBH : 0 ≤ D * (R ω * (B ω * H ω)) := mul_nonneg hD hRBH0
    calc
      _ ≤ ENNReal.ofReal (β * V ω ^ 2 + D * (R ω * (B ω * H ω))) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = _ := by
        rw [ENNReal.ofReal_add hβV hDRBH,
          ENNReal.ofReal_mul hβ,
          ENNReal.ofReal_mul hD,
          ENNReal.ofReal_mul (hR0 ω),
          ENNReal.ofReal_mul (hB0 ω)]
        ring
  have hbase :
      ∫⁻ ω, ENNReal.ofReal β * ENNReal.ofReal (V ω ^ 2) ∂μ ≤
        ENNReal.ofReal β * ENNReal.ofReal ξ := by
    rw [lintegral_const_mul'' _ hV2meas]
    exact mul_le_mul_of_nonneg_left hVsource (by simp)
  have hrare :
      ∫⁻ ω, ENNReal.ofReal D *
          (ENNReal.ofReal (R ω) * ENNReal.ofReal (B ω) * ENNReal.ofReal (H ω)) ∂μ ≤
        ENNReal.ofReal D *
          (ENNReal.ofReal Hcap * (ENNReal.ofReal ε * ENNReal.ofReal β)) := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact mul_le_mul_of_nonneg_left hRBH (by simp)
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal β * ENNReal.ofReal (V ω ^ 2) +
        ENNReal.ofReal D *
          (ENNReal.ofReal (R ω) * ENNReal.ofReal (B ω) * ENNReal.ofReal (H ω)) ∂μ :=
      lintegral_mono fun ω => hpoint ω
    _ = ∫⁻ ω, ENNReal.ofReal β * ENNReal.ofReal (V ω ^ 2) ∂μ +
        ∫⁻ ω, ENNReal.ofReal D *
          (ENNReal.ofReal (R ω) * ENNReal.ofReal (B ω) * ENNReal.ofReal (H ω)) ∂μ :=
      lintegral_add_left' hbaseMeas _
    _ ≤ ENNReal.ofReal β * ENNReal.ofReal ξ +
        ENNReal.ofReal D *
          (ENNReal.ofReal Hcap * (ENNReal.ofReal ε * ENNReal.ofReal β)) :=
      add_le_add hbase hrare
    _ = ENNReal.ofReal (β * ξ + ε * D * β * Hcap) := by
      have hrareEq : ENNReal.ofReal D *
          (ENNReal.ofReal Hcap * (ENNReal.ofReal ε * ENNReal.ofReal β)) =
            ENNReal.ofReal (ε * D * β * Hcap) := by
        rw [← ENNReal.ofReal_mul hε, ← ENNReal.ofReal_mul hHcap,
          ← ENNReal.ofReal_mul hD]
        congr 1
        ring
      rw [hrareEq, ← ENNReal.ofReal_mul hβ]
      exact (ENNReal.ofReal_add (mul_nonneg hβ hξ)
        (show 0 ≤ ε * D * β * Hcap by positivity)).symm

end ASDExplicitGamma.Inverse
