module

public import ASDExplicitGamma.Native.HeatStepChildCap

/-! The pathwise sharp frame map for an arbitrary elliptic coefficient field on a cell, and its
`L^20` transfer from `σ̄_m` to `σ̄_{m+1}`. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open Homogenization Algsuperdiff.Section3 MeasureTheory
open ASDExplicitGamma.Variational ASDExplicitGamma.Numerics.Native
open scoped ENNReal
open ASDExplicitGamma.Gaussian

/-- The two block traces of an elliptic coarse response are strictly positive. -/
private theorem nativeHeatStepAT_trace_pos {Q : TriadicCube 2} {nu Lambda : ℝ}
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
private theorem nativeHeatStepAT_trace_product {Q : TriadicCube 2} {nu Lambda : ℝ}
    {a : CoeffField 2} (hnu : 0 < nu)
    (hEll : IsEllipticFieldOn nu Lambda (cubeSet Q) a) :
    4 ≤ Matrix.trace (coarseBlockMatrix (cubeSet Q) a).upperLeft *
      Matrix.trace (coarseBlockMatrix (cubeSet Q) a).lowerRight := by
  have hpos := nativeHeatStepAT_trace_pos hnu hEll
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


/-- Pathwise sharp frame map from `σ̄_m` to `σ̄_{m+1}` for the completed cutoff `N`. -/
theorem nativeHeatStep_sharpPathwise_field (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) {Lambda : ℝ}
    (a : CoeffField 2) (hEll : IsEllipticFieldOn M.nu Lambda (cubeSet Q) a) :
    let rho : ℝ := (Annealed.sigmaBar M (m + 1) : ℝ) / (Annealed.sigmaBar M m : ℝ)
    let T0 : ℝ := traceDefect (cubeSet Q) a (Annealed.sigmaBar M m : ℝ)
    traceDefect (cubeSet Q) a (Annealed.sigmaBar M (m + 1) : ℝ) ≤
      (rho + rho⁻¹) / 2 * T0 + (rho - rho⁻¹) / 2 * Real.sqrt (T0 * (T0 + 8)) +
        4 * ((rho + rho⁻¹) / 2 - 1) := by
  dsimp only
  let A := coarseBlockMatrix (cubeSet Q) a
  let sigmaK : ℝ := Annealed.sigmaBar M m
  let sigmaM : ℝ := Annealed.sigmaBar M (m + 1)
  let rho : ℝ := sigmaM / sigmaK
  let x : ℝ := sigmaK⁻¹ * Matrix.trace A.upperLeft
  let y : ℝ := sigmaK * Matrix.trace A.lowerRight
  have htrpos := nativeHeatStepAT_trace_pos M.nu_pos hEll
  have hsigmaK : 0 < sigmaK := (Annealed.sigmaBar_characterization M m).1
  have hratio : 1 ≤ rho := by
    have h := (ASDExplicitGamma.Scalar.sigmaBar_structural_continuity_nat M m 1).1
    simpa [rho, sigmaK, sigmaM] using h
  have hx : 0 < x := mul_pos (inv_pos.mpr hsigmaK) htrpos.1
  have hy : 0 < y := mul_pos hsigmaK htrpos.2
  have hprod : 4 ≤ x * y := by
    have hp := nativeHeatStepAT_trace_product M.nu_pos hEll
    have hcancel : x * y = Matrix.trace A.upperLeft * Matrix.trace A.lowerRight := by
      dsimp [x, y]
      field_simp [hsigmaK.ne']
    rw [hcancel]
    exact hp
  have hsigmaM : sigmaM ≠ 0 := (Annealed.sigmaBar M (m + 1)).2.ne'
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


/-- The `L^20` transfer of a trace cap from the frame `σ̄_m` to `σ̄_{m+1}` given the pathwise
sharp frame map. -/
theorem nativeHeatStep_frameTransfer (M : ABKModel 2) (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (T Tn : Cutoff.CutoffSample 2 → ℝ) (hTm : Measurable T) (hTnm : Measurable Tn)
    (hT0 : ∀ ω, 0 ≤ T ω) (hTn0 : ∀ ω, 0 ≤ Tn ω)
    (hpath : ∀ ω, let rho : ℝ := (Annealed.sigmaBar M (m + 1) : ℝ) / (Annealed.sigmaBar M m : ℝ)
      Tn ω ≤ (rho + rho⁻¹) / 2 * T ω + (rho - rho⁻¹) / 2 * Real.sqrt (T ω * (T ω + 8)) +
        4 * ((rho + rho⁻¹) / 2 - 1))
    (tq : ℚ) (htq0 : (0 : ℝ) ≤ (tq : ℝ)) (hroot : nativeRootValid (tq * (tq + 8)) 2 = true)
    (hL : eLpNorm' T 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (tq : ℝ)) :
    eLpNorm' Tn 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal ((nativeShiftedFrame 1 tq : ℚ) : ℝ) := by
  classical
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  letI : IsProbabilityMeasure μ := (Cutoff.cutoffSampleLaw M).property
  set a : ℝ := (((11 / 10) * (2 * nativeGamma * ((1 : ℕ) : ℚ)) : ℚ) : ℝ) with ha
  have ha0 : 0 ≤ a := by rw [ha]; norm_num [nativeGamma]
  have ha1 : a < 1 := by rw [ha]; norm_num [nativeGamma]
  set r : ℝ := 1 / (1 - a) with hr
  have hr1 : 1 ≤ r := by
    rw [hr, le_div_iff₀ (by linarith)]
    linarith
  have hrho := nativeHeatRefined_ratio_le M hg
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
    set rho : ℝ := (Annealed.sigmaBar M (m + 1) : ℝ) / (Annealed.sigmaBar M m : ℝ) with hrhodef
    have hrho1 : 1 ≤ rho := by
      have h1 := (ASDExplicitGamma.Scalar.sigmaBar_structural_continuity_nat M m 1).1
      simpa [rho] using h1
    have hrhoR : rho ≤ r := by
      have h2 := (ASDExplicitGamma.Scalar.sigmaBar_structural_continuity_nat M m 1).2
      have h2' : rho ≤ Real.rpow 3 (2 * M.gamma * ((1 : ℕ) : ℝ)) := by simpa [rho] using h2
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
  refine hfinal.trans (ENNReal.ofReal_le_ofReal ?_)
  have hd' : 0 ≤ (11 / 10) * (2 * nativeGamma * ((1 : ℕ) : ℚ)) ∧
      (11 / 10) * (2 * nativeGamma * ((1 : ℕ) : ℚ)) < 1 := by
    norm_num [nativeGamma]
  have hsound := nativeShiftedFrame_sound 1 tq hd' hroot
  refine le_trans (le_of_eq ?_) hsound
  simp [nativeFrameReal, c, d, r, a, one_div]

end ASDExplicitGamma.Native
