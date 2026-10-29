module

public import ASDExplicitGamma.Native.HeatStepAllTimeFrame

/-! NA-RETURNS: the sharp pathwise frame map and its `L^20` transfer from `σ̄_K` to `σ̄_{K+h}`
for an arbitrary gap `1 ≤ h ≤ 1334` (the one-step version is `HeatStepAllTimeFrame`). -/

@[expose] public section

namespace ASDExplicitGamma.Native

open Homogenization Algsuperdiff.Section3 MeasureTheory
open ASDExplicitGamma.Variational ASDExplicitGamma.Numerics.Native
open scoped ENNReal
open ASDExplicitGamma.Gaussian

/-- The two block traces of an elliptic coarse response are strictly positive. -/
private theorem nativeReturnsFrameAT_trace_pos {Q : TriadicCube 2} {nu Lambda : ℝ}
    {a : CoeffField 2} (hnu : 0 < nu)
    (hEll : IsEllipticFieldOn nu Lambda (cubeSet Q) a) :
    0 < Matrix.trace (coarseBlockMatrix (cubeSet Q) a).upperLeft ∧
    0 < Matrix.trace (coarseBlockMatrix (cubeSet Q) a).lowerRight := by
  let A := coarseBlockMatrix (cubeSet Q) a
  have hA : (toFullBlockMat A).PosDef := coarseBlockMatrix_posDef hnu hEll
  have hu0 : 0 < A.upperLeft 0 0 := by
    have h := hA.diag_pos (i := Sum.inl (0 : Fin 2))
    simpa [toFullBlockMat, A] using h
  have hu1 : 0 < A.upperLeft 1 1 := by
    have h := hA.diag_pos (i := Sum.inl (1 : Fin 2))
    simpa [toFullBlockMat, A] using h
  have hl0 : 0 < A.lowerRight 0 0 := by
    have h := hA.diag_pos (i := Sum.inr (0 : Fin 2))
    simpa [toFullBlockMat, A] using h
  have hl1 : 0 < A.lowerRight 1 1 := by
    have h := hA.diag_pos (i := Sum.inr (1 : Fin 2))
    simpa [toFullBlockMat, A] using h
  constructor
  · simpa [A, Matrix.trace, Fin.sum_univ_two] using add_pos hu0 hu1
  · simpa [A, Matrix.trace, Fin.sum_univ_two] using add_pos hl0 hl1

/-- Ellipticity and pointwise nonnegativity at a freely chosen positive frame
give the source trace-product bound. -/
private theorem nativeReturnsFrameAT_trace_product {Q : TriadicCube 2} {nu Lambda : ℝ}
    {a : CoeffField 2} (hnu : 0 < nu)
    (hEll : IsEllipticFieldOn nu Lambda (cubeSet Q) a) :
    4 ≤ Matrix.trace (coarseBlockMatrix (cubeSet Q) a).upperLeft *
      Matrix.trace (coarseBlockMatrix (cubeSet Q) a).lowerRight := by
  have hpos := nativeReturnsFrameAT_trace_pos hnu hEll
  let U := Matrix.trace (coarseBlockMatrix (cubeSet Q) a).upperLeft
  let V := Matrix.trace (coarseBlockMatrix (cubeSet Q) a).lowerRight
  let sigma : ℝ := 2 / V
  have hsigma : 0 < sigma := by
    dsimp [sigma]
    exact div_pos (by norm_num) hpos.2
  have hdef := traceDefect_nonneg_of_ellipticFieldOn_triCube hnu hEll hsigma
  have hinv : sigma⁻¹ = V / 2 := by
    dsimp [sigma]
    field_simp [hpos.2.ne']
  have hscale : sigma * V = 2 := by
    dsimp [sigma]
    field_simp [hpos.2.ne']
    exact mul_inv_cancel₀ hpos.2.ne'
  change 0 ≤ sigma⁻¹ * U + sigma * V - 4 at hdef
  rw [hinv, hscale] at hdef
  dsimp [U, V] at hdef ⊢
  nlinarith



/-- Pathwise sharp frame map from `σ̄_K` to `σ̄_{K+h}`. -/
theorem nativeReturns_sharpPathwise_field (M : ABKModel 2) (K : ℤ) (h : ℕ) (Q : TriadicCube 2)
    {Lambda : ℝ} (a : CoeffField 2) (hEll : IsEllipticFieldOn M.nu Lambda (cubeSet Q) a) :
    let rho : ℝ := (Annealed.sigmaBar M (K + (h : ℤ)) : ℝ) / (Annealed.sigmaBar M K : ℝ)
    let T0 : ℝ := traceDefect (cubeSet Q) a (Annealed.sigmaBar M K : ℝ)
    traceDefect (cubeSet Q) a (Annealed.sigmaBar M (K + (h : ℤ)) : ℝ) ≤
      (rho + rho⁻¹) / 2 * T0 + (rho - rho⁻¹) / 2 * Real.sqrt (T0 * (T0 + 8)) +
        4 * ((rho + rho⁻¹) / 2 - 1) := by
  dsimp only
  let A := coarseBlockMatrix (cubeSet Q) a
  let sigmaK : ℝ := Annealed.sigmaBar M K
  let sigmaM : ℝ := Annealed.sigmaBar M (K + (h : ℤ))
  let rho : ℝ := sigmaM / sigmaK
  let x : ℝ := sigmaK⁻¹ * Matrix.trace A.upperLeft
  let y : ℝ := sigmaK * Matrix.trace A.lowerRight
  have htrpos := nativeReturnsFrameAT_trace_pos M.nu_pos hEll
  have hsigmaK : 0 < sigmaK := (Annealed.sigmaBar_characterization M K).1
  have hratio : 1 ≤ rho := by
    have h1 := (ASDExplicitGamma.Scalar.sigmaBar_structural_continuity_nat M K h).1
    simpa [rho, sigmaK, sigmaM] using h1
  have hx : 0 < x := mul_pos (inv_pos.mpr hsigmaK) htrpos.1
  have hy : 0 < y := mul_pos hsigmaK htrpos.2
  have hprod : 4 ≤ x * y := by
    have hp := nativeReturnsFrameAT_trace_product M.nu_pos hEll
    have hcancel : x * y = Matrix.trace A.upperLeft * Matrix.trace A.lowerRight := by
      dsimp [x, y]
      field_simp [hsigmaK.ne']
    rw [hcancel]
    exact hp
  have hsigmaM : sigmaM ≠ 0 := (Annealed.sigmaBar M (K + (h : ℤ))).2.ne'
  have hxdiv : x / rho = sigmaM⁻¹ * Matrix.trace A.upperLeft := by
    dsimp [x, rho]
    field_simp [hsigmaK.ne', hsigmaM]
  have hydiv : rho * y = sigmaM * Matrix.trace A.lowerRight := by
    dsimp [rho, y]
    field_simp [hsigmaK.ne']
  have hnew : traceDefect (cubeSet Q) a sigmaM = x / rho + rho * y - 4 := by
    change sigmaM⁻¹ * Matrix.trace A.upperLeft +
      sigmaM * Matrix.trace A.lowerRight - 4 = _
    rw [← hxdiv, ← hydiv]
  have hold : traceDefect (cubeSet Q) a sigmaK = x + y - 4 := by
    dsimp [x, y, sigmaK, A]
    unfold traceDefect
    field_simp [hsigmaK.ne']
  rw [hnew, hold]
  exact nativeHeatRefined_sharpFrameScalar hx hy hprod hratio

/-- The structural ratio is below the rational frame factor, for every gap `h ≤ 1334`. -/
theorem nativeReturns_ratio_le (M : ABKModel 2) (hg : M.gamma ≤ gammaZero) (h : ℕ)
    (hh : h ≤ 1334) :
    Real.rpow 3 (2 * M.gamma * (h : ℝ)) ≤
      1 / (1 - (((11 / 10) * (2 * nativeGamma * (h : ℚ)) : ℚ) : ℝ)) := by
  have hγ : 0 ≤ M.gamma := M.shellPrefix.gamma_pos.le
  have hg0 : M.gamma ≤ 17 / 50000 := by simpa [gammaZero] using hg
  have hhR : (h : ℝ) ≤ 1334 := by exact_mod_cast hh
  set a : ℝ := (((11 / 10) * (2 * nativeGamma * (h : ℚ)) : ℚ) : ℝ) with ha
  have ha' : a = (11 / 10) * (2 * (17 / 50000 : ℝ) * (h : ℝ)) := by
    rw [ha]; push_cast; norm_num [nativeGamma]
  have ha1 : a < 1 := by
    rw [ha']
    have : (2 * (17 / 50000 : ℝ) * (h : ℝ)) ≤ 2 * (17 / 50000 : ℝ) * 1334 := by gcongr
    linarith
  have hlog : Real.log 3 ≤ 11 / 10 := by
    have := Real.log_three_lt_d9
    norm_num at this ⊢
    linarith
  have hx : 2 * M.gamma * (h : ℝ) * Real.log 3 ≤ a := by
    rw [ha']
    have h1 : 2 * M.gamma * (h : ℝ) ≤ 2 * (17 / 50000 : ℝ) * (h : ℝ) := by gcongr
    have h2 : 0 ≤ 2 * M.gamma * (h : ℝ) := by positivity
    calc
      _ ≤ (2 * (17 / 50000 : ℝ) * (h : ℝ)) * (11 / 10) :=
        mul_le_mul h1 hlog (Real.log_nonneg (by norm_num)) (by positivity)
      _ = _ := by ring
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
theorem nativeReturns_frameTransfer (M : ABKModel 2) (hg : M.gamma ≤ gammaZero) (K : ℤ)
    (h : ℕ) (hh : h ≤ 1334)
    (T Tn : Cutoff.CutoffSample 2 → ℝ) (hTm : Measurable T) (hTnm : Measurable Tn)
    (hT0 : ∀ ω, 0 ≤ T ω) (hTn0 : ∀ ω, 0 ≤ Tn ω)
    (hpath : ∀ ω, let rho : ℝ := (Annealed.sigmaBar M (K + (h : ℤ)) : ℝ) / (Annealed.sigmaBar M K : ℝ)
      Tn ω ≤ (rho + rho⁻¹) / 2 * T ω + (rho - rho⁻¹) / 2 * Real.sqrt (T ω * (T ω + 8)) +
        4 * ((rho + rho⁻¹) / 2 - 1))
    (tq : ℚ) (htq0 : (0 : ℝ) ≤ (tq : ℝ))
    (hL : eLpNorm' T 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (tq : ℝ)) :
    eLpNorm' Tn 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (nativeFrameReal (((11 / 10) * (2 * nativeGamma * (h : ℚ)) : ℚ) : ℝ) (tq : ℝ)) := by
  classical
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  letI : IsProbabilityMeasure μ := (Cutoff.cutoffSampleLaw M).property
  set a : ℝ := (((11 / 10) * (2 * nativeGamma * (h : ℚ)) : ℚ) : ℝ) with ha
  have ha0 : 0 ≤ a := by rw [ha]; push_cast; norm_num [nativeGamma]
  have hhR : (h : ℝ) ≤ 1334 := by exact_mod_cast hh
  have ha1 : a < 1 := by
    rw [ha]; push_cast; norm_num [nativeGamma]
    have : (2 * (17 / 50000 : ℝ) * (h : ℝ)) ≤ 2 * (17 / 50000 : ℝ) * 1334 := by gcongr
    linarith
  set r : ℝ := 1 / (1 - a) with hr
  have hr1 : 1 ≤ r := by
    rw [hr, le_div_iff₀ (by linarith)]
    linarith
  have hrho := nativeReturns_ratio_le M hg h hh
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
    htq0 hpt hL
  refine hfinal.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  simp [nativeFrameReal, c, d, r, a, one_div]

/-- Measurability of the cutoff trace defect in an arbitrary frame. -/
theorem nativeReturns_traceDefect_measurable (M : ABKModel 2) (n q : ℤ) (σ : ℝ) :
    Measurable (fun ω : Cutoff.CutoffSample 2 =>
      traceDefect (cubeSet (originCube 2 q)) (Cutoff.coefficientCutoff M.nu n ω).toFun σ) := by
  let X : Cutoff.CutoffSample 2 → RegCoeffField 2 := Cutoff.coefficientCutoff M.nu n
  have hX : Measurable X := by simpa [X] using Cutoff.measurable_coefficientCutoff M.nu n
  have hEll : ∀ ω, Book.Ch04.AELocallyUniformlyEllipticField (X ω) := by
    intro ω
    simpa [X] using Cutoff.coefficientCutoff_aeLocallyUniformlyEllipticField M n ω
  let Q : TriadicCube 2 := originCube 2 q
  have hUL := Algsuperdiff.Section3.Provider.BadEvents.measurable_comp_coarseB_cubeSet
    hX hEll Q
  have hLR := Algsuperdiff.Section3.Provider.BadEvents.measurable_comp_coarseSigmaStarInv_cubeSet
    hX hEll Q
  have hTraceUL : Measurable (fun ω : Cutoff.CutoffSample 2 =>
      Matrix.trace ((coarseBlockMatrix (cubeSet Q) (X ω).toFun).upperLeft)) := by
    change Measurable (fun ω => ∑ i ∈ Finset.univ,
      (coarseBlockMatrix (cubeSet Q) (X ω).toFun).upperLeft i i)
    apply Finset.measurable_sum
    intro i hi
    exact (measurable_pi_iff.mp (measurable_pi_iff.mp hUL i)) i
  have hTraceLR : Measurable (fun ω : Cutoff.CutoffSample 2 =>
      Matrix.trace ((coarseBlockMatrix (cubeSet Q) (X ω).toFun).lowerRight)) := by
    change Measurable (fun ω => ∑ i ∈ Finset.univ,
      (coarseBlockMatrix (cubeSet Q) (X ω).toFun).lowerRight i i)
    apply Finset.measurable_sum
    intro i hi
    exact (measurable_pi_iff.mp (measurable_pi_iff.mp hLR i)) i
  change Measurable (fun ω =>
    σ⁻¹ * Matrix.trace (coarseBlockMatrix (cubeSet Q) (X ω).toFun).upperLeft +
      σ * Matrix.trace (coarseBlockMatrix (cubeSet Q) (X ω).toFun).lowerRight - 4)
  exact (hTraceUL.const_mul _).add (hTraceLR.const_mul _) |>.sub measurable_const

/-- The frozen cutoff trace, from an old-frame bound on the same coefficient (cube `q`,
cutoff `K+h`, frame `σ̄_K`) in the extended `L^20` norm. -/
theorem nativeReturns_cutoffTrace_frame (M : ABKModel 2) (hg : M.gamma ≤ gammaZero) (K : ℤ)
    (h : ℕ) (hh : h ≤ 1334) (q : ℤ) (tq : ℚ) (htq0 : (0 : ℝ) ≤ (tq : ℝ))
    (hL : eLpNorm (fun ω : Cutoff.CutoffSample 2 =>
        traceDefect (cubeSet (originCube 2 q))
          (Cutoff.coefficientCutoff M.nu (K + (h : ℤ)) ω).toFun (Annealed.sigmaBar M K : ℝ))
      20 (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (tq : ℝ)) :
    eLpNorm (cutoffTraceDefect M (K + (h : ℤ)) q) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (nativeFrameReal (((11 / 10) * (2 * nativeGamma * (h : ℚ)) : ℚ) : ℝ)
        (tq : ℝ)) := by
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
  refine nativeReturns_frameTransfer M hg K h hh _ _ hTm hTnm hT0
    (cutoffTraceDefect_nonneg M (K + (h : ℤ)) q) ?_ tq htq0 hL
  intro ω
  obtain ⟨Λ, hEll⟩ := cutoff_isEllipticFieldOn_cube M (K + (h : ℤ)) ω (originCube 2 q)
  exact nativeReturns_sharpPathwise_field M K h (originCube 2 q) _ hEll

end ASDExplicitGamma.Native
