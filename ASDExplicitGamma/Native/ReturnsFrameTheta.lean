module

public import ASDExplicitGamma.Native.ReturnsFrame
public import ASDExplicitGamma.Native.HeatStepThetaRow
public import ASDExplicitGamma.Numerics.Native.FrameTheta

/-! NA-RETURNS at smaller gamma: the `L^20` transfer of a theta-scaled trace cap from `σ̄_K` to
`σ̄_{K+h}`, `F(θa,θt) ≤ θ F(a,t)`. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open Homogenization Algsuperdiff.Section3 MeasureTheory
open ASDExplicitGamma.Variational ASDExplicitGamma.Numerics.Native
open scoped ENNReal
open ASDExplicitGamma.Gaussian

/-- The structural ratio is below the rational frame factor, for every gap `h ≤ 1334`. -/
theorem nativeReturns_ratio_le_theta (M : ABKModel 2) (hg : M.gamma ≤ gammaZero) (h : ℕ)
    (hh : h ≤ 1334) :
    Real.rpow 3 (2 * M.gamma * (h : ℝ)) ≤
      1 / (1 - theta M * (((11 / 10) * (2 * nativeGamma * (h : ℚ)) : ℚ) : ℝ)) := by
  obtain ⟨hτ0, hτ1⟩ := theta_pos_le_one M hg
  have hγ : 0 ≤ M.gamma := M.shellPrefix.gamma_pos.le
  have hg0 : M.gamma ≤ 17 / 50000 := by simpa [gammaZero] using hg
  have hhR : (h : ℝ) ≤ 1334 := by exact_mod_cast hh
  set a : ℝ := theta M * (((11 / 10) * (2 * nativeGamma * (h : ℚ)) : ℚ) : ℝ) with ha
  have ha' : a = (11 / 10) * (2 * M.gamma * (h : ℝ)) := by
    rw [ha]; unfold theta gammaZero; push_cast; norm_num [nativeGamma]; ring
  have ha1 : a < 1 := by
    rw [ha']
    have : (2 * M.gamma * (h : ℝ)) ≤ 2 * (17 / 50000 : ℝ) * 1334 := by gcongr
    linarith
  have hlog : Real.log 3 ≤ 11 / 10 := by
    have := Real.log_three_lt_d9
    norm_num at this ⊢
    linarith
  have hx : 2 * M.gamma * (h : ℝ) * Real.log 3 ≤ a := by
    rw [ha']
    have h2 : 0 ≤ 2 * M.gamma * (h : ℝ) := by positivity
    nlinarith
  have hexp : Real.rpow 3 (2 * M.gamma * (h : ℝ)) =
      Real.exp (2 * M.gamma * (h : ℝ) * Real.log 3) := by
    change (3 : ℝ) ^ (2 * M.gamma * (h : ℝ)) = _
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    ring_nf
  rw [hexp]
  have hle : Real.exp (2 * M.gamma * (h : ℝ) * Real.log 3) ≤ Real.exp a :=
    Real.exp_le_exp.mpr hx
  have hden : 0 < 1 - a := by linarith
  have hkey : Real.exp a * (1 - a) ≤ 1 := by
    have h := Real.one_sub_le_exp_neg a
    have hpos := Real.exp_pos a
    have : Real.exp a * (1 - a) ≤ Real.exp a * Real.exp (-a) :=
      mul_le_mul_of_nonneg_left h hpos.le
    rw [← Real.exp_add] at this
    simpa using this
  refine hle.trans ?_
  rw [le_div_iff₀ hden]
  exact hkey

/-- The `L^20` transfer of a trace cap from `σ̄_K` to `σ̄_{K+h}`, with the sharp frame map. -/
theorem nativeReturns_frameTransfer_theta (M : ABKModel 2) (hg : M.gamma ≤ gammaZero) (K : ℤ)
    (h : ℕ) (hh : h ≤ 1334)
    (T Tn : Cutoff.CutoffSample 2 → ℝ) (hTm : Measurable T) (hTnm : Measurable Tn)
    (hT0 : ∀ ω, 0 ≤ T ω) (hTn0 : ∀ ω, 0 ≤ Tn ω)
    (hpath : ∀ ω, let rho : ℝ := (Annealed.sigmaBar M (K + (h : ℤ)) : ℝ) / (Annealed.sigmaBar M K : ℝ)
      Tn ω ≤ (rho + rho⁻¹) / 2 * T ω + (rho - rho⁻¹) / 2 * Real.sqrt (T ω * (T ω + 8)) +
        4 * ((rho + rho⁻¹) / 2 - 1))
    (tq : ℚ) (htq0 : (0 : ℝ) ≤ (tq : ℝ))
    (hL : eLpNorm' T 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (theta M * (tq : ℝ))) :
    eLpNorm' Tn 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (theta M * nativeFrameReal
        (((11 / 10) * (2 * nativeGamma * (h : ℚ)) : ℚ) : ℝ) (tq : ℝ)) := by
  classical
  obtain ⟨hτ0, hτ1⟩ := theta_pos_le_one M hg
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  letI : IsProbabilityMeasure μ := (Cutoff.cutoffSampleLaw M).property
  set a0 : ℝ := (((11 / 10) * (2 * nativeGamma * (h : ℚ)) : ℚ) : ℝ) with ha0def
  have ha00 : 0 ≤ a0 := by rw [ha0def]; push_cast; norm_num [nativeGamma]
  have hhR : (h : ℝ) ≤ 1334 := by exact_mod_cast hh
  have ha01 : a0 < 1 := by
    rw [ha0def]; push_cast; norm_num [nativeGamma]
    have : (2 * (17 / 50000 : ℝ) * (h : ℝ)) ≤ 2 * (17 / 50000 : ℝ) * 1334 := by gcongr
    linarith
  set a : ℝ := theta M * a0 with hadef
  have ha0 : 0 ≤ a := mul_nonneg hτ0.le ha00
  have ha1 : a < 1 := lt_of_le_of_lt (mul_le_of_le_one_left ha00 hτ1) ha01
  set r : ℝ := 1 / (1 - a) with hr
  have hr1 : 1 ≤ r := by
    rw [hr, le_div_iff₀ (by linarith)]
    linarith
  have hrho := nativeReturns_ratio_le_theta M hg h hh
  set c : ℝ := (r + r⁻¹) / 2
  set d : ℝ := (r - r⁻¹) / 2
  have hrpos : 0 < r := by linarith
  have hrinv0 : 0 < r⁻¹ := inv_pos.mpr hrpos
  have hrinv : r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hr1
  have hc0 : 0 ≤ c := by show 0 ≤ (r + r⁻¹) / 2; linarith
  have hd0 : 0 ≤ d := by show 0 ≤ (r - r⁻¹) / 2; linarith
  have hc1 : 1 ≤ c := by
    show 1 ≤ (r + r⁻¹) / 2
    have hmul : r * r⁻¹ = 1 := mul_inv_cancel₀ hrpos.ne'
    nlinarith [sq_nonneg (r - r⁻¹)]
  have hpt : ∀ ω, Tn ω ≤ c * T ω + d * Real.sqrt (T ω * (T ω + 8)) + 4 * (c - 1) := by
    intro ω
    have hp := hpath ω
    dsimp only at hp
    set rho : ℝ := (Annealed.sigmaBar M (K + (h : ℤ)) : ℝ) / (Annealed.sigmaBar M K : ℝ) with hrhodef
    have hrho1 : 1 ≤ rho := by
      have h1 := (ASDExplicitGamma.Scalar.sigmaBar_structural_continuity_nat M K h).1
      simpa [rho] using h1
    have hrhoR : rho ≤ r := by
      have h2 := (ASDExplicitGamma.Scalar.sigmaBar_structural_continuity_nat M K h).2
      have h2' : rho ≤ Real.rpow 3 (2 * M.gamma * (h : ℝ)) := by simpa [rho] using h2
      exact h2'.trans hrho
    obtain ⟨hmc0, hmd0⟩ := nativeHeatRefined_frameCoeff_mono hrho1 hrhoR
    have hmc : (rho + rho⁻¹) / 2 ≤ c := hmc0
    have hmd : (rho - rho⁻¹) / 2 ≤ d := hmd0
    have hT := hT0 ω
    have hsq : 0 ≤ Real.sqrt (T ω * (T ω + 8)) := Real.sqrt_nonneg _
    have e1 := mul_le_mul_of_nonneg_right hmc hT
    have e2 := mul_le_mul_of_nonneg_right hmd hsq
    have e3 : 4 * ((rho + rho⁻¹) / 2 - 1) ≤ 4 * (c - 1) := by linarith
    have hp' : Tn ω ≤
        (rho + rho⁻¹) / 2 * T ω + (rho - rho⁻¹) / 2 * Real.sqrt (T ω * (T ω + 8)) +
          4 * ((rho + rho⁻¹) / 2 - 1) := hp
    linarith
  have hfinal := nativeHeatRefined_eLpNorm'_frame_le hTm hTnm hT0 hTn0 hc0 hd0 (by linarith)
    (mul_nonneg hτ0.le htq0) hpt hL
  refine hfinal.trans (ENNReal.ofReal_le_ofReal ?_)
  have hform : c * (theta M * (tq : ℝ)) + d * Real.sqrt ((theta M * (tq : ℝ)) *
      ((theta M * (tq : ℝ)) + 8)) + 4 * (c - 1) =
      nativeFrameReal (theta M * a0) (theta M * (tq : ℝ)) := by
    simp [nativeFrameReal, c, d, r, a, one_div]
  rw [hform]
  exact native_frame_theta a0 (tq : ℝ) (theta M) ha00 ha01 htq0 hτ0.le hτ1


/-- The frozen cutoff trace, from an old-frame bound on the same coefficient (cube `q`,
cutoff `K+h`, frame `σ̄_K`) in the extended `L^20` norm. -/
theorem nativeReturns_cutoffTrace_frame_theta (M : ABKModel 2) (hg : M.gamma ≤ gammaZero) (K : ℤ)
    (h : ℕ) (hh : h ≤ 1334) (q : ℤ) (tq : ℚ) (htq0 : (0 : ℝ) ≤ (tq : ℝ))
    (hL : eLpNorm (fun ω : Cutoff.CutoffSample 2 =>
        traceDefect (cubeSet (originCube 2 q))
          (Cutoff.coefficientCutoff M.nu (K + (h : ℤ)) ω).toFun (Annealed.sigmaBar M K : ℝ))
      20 (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (theta M * (tq : ℝ))) :
    eLpNorm (cutoffTraceDefect M (K + (h : ℤ)) q) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (theta M * nativeFrameReal
        (((11 / 10) * (2 * nativeGamma * (h : ℚ)) : ℚ) : ℝ) (tq : ℝ)) := by
  have hTm := nativeReturns_traceDefect_measurable M (K + (h : ℤ)) q (Annealed.sigmaBar M K : ℝ)
  have hTnm := cutoffTraceDefect_measurable M (K + (h : ℤ)) q
  have hT0 : ∀ ω, 0 ≤ traceDefect (cubeSet (originCube 2 q))
      (Cutoff.coefficientCutoff M.nu (K + (h : ℤ)) ω).toFun (Annealed.sigmaBar M K : ℝ) := by
    intro ω
    obtain ⟨Λ, hEll⟩ := cutoff_isEllipticFieldOn_cube M (K + (h : ℤ)) ω (originCube 2 q)
    exact traceDefect_nonneg_of_ellipticFieldOn_triCube M.nu_pos hEll
      (Annealed.sigmaBar_characterization M K).1
  rw [eLpNorm_eq_eLpNorm' (by norm_num : (20 : ℝ≥0∞) ≠ 0) (by norm_num : (20 : ℝ≥0∞) ≠ ⊤)
    hTnm.aestronglyMeasurable]
  rw [eLpNorm_eq_eLpNorm' (by norm_num : (20 : ℝ≥0∞) ≠ 0) (by norm_num : (20 : ℝ≥0∞) ≠ ⊤)
    hTm.aestronglyMeasurable] at hL
  simp only [ENNReal.toReal_ofNat] at hL ⊢
  refine nativeReturns_frameTransfer_theta M hg K h hh _ _ hTm hTnm hT0
    (cutoffTraceDefect_nonneg M (K + (h : ℤ)) q) ?_ tq htq0 hL
  intro ω
  obtain ⟨Λ, hEll⟩ := cutoff_isEllipticFieldOn_cube M (K + (h : ℤ)) ω (originCube 2 q)
  exact nativeReturns_sharpPathwise_field M K h (originCube 2 q) _ hEll

end ASDExplicitGamma.Native
