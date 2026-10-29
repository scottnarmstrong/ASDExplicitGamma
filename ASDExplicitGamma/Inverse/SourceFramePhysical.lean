module

public import ASDExplicitGamma.Inverse.SourceFrameScalar

/-! Exact-gap pathwise source framing for the actual completed coefficient. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization Algsuperdiff.Section3 MeasureTheory
open ASDExplicitGamma.Variational
noncomputable section

/-- The two block traces of an elliptic coarse response are strictly positive. -/
private theorem source_coarse_block_trace_pos {Q : TriadicCube 2} {nu Lambda : ℝ}
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
private theorem source_coarse_block_trace_product {Q : TriadicCube 2} {nu Lambda : ℝ}
    {a : CoeffField 2} (hnu : 0 < nu)
    (hEll : IsEllipticFieldOn nu Lambda (cubeSet Q) a) :
    4 ≤ Matrix.trace (coarseBlockMatrix (cubeSet Q) a).upperLeft *
      Matrix.trace (coarseBlockMatrix (cubeSet Q) a).lowerRight := by
  have hpos := source_coarse_block_trace_pos hnu hEll
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

/-- Pointwise restoration for an actual completed cutoff coefficient. Every
child cube uses the same true scalar frames; no molecular-frame normalization
is introduced. -/
theorem source_cutoff_pathwise_frame_map (M : ABKModel 2) (K m n : ℤ)
    (omega : Cutoff.CutoffSample 2) (hKm : K ≤ m) (eta : ℝ) (heta : 0 < eta) :
    cutoffTraceDefect M m n omega ≤
      ((Annealed.sigmaBar M m : ℝ) / (Annealed.sigmaBar M K : ℝ)) *
        ((1 + eta) * traceDefect (cubeSet (originCube 2 n))
            (Cutoff.coefficientCutoff M.nu m omega).toFun
            (Annealed.sigmaBar M K : ℝ) +
          8 * (1 + 1 / eta) *
            ((11 / 10 : ℝ) * M.gamma * (m - K : ℝ)) ^ 2) := by
  let A := coarseBlockMatrix (cubeSet (originCube 2 n))
    (Cutoff.coefficientCutoff M.nu m omega).toFun
  let sigmaK : ℝ := Annealed.sigmaBar M K
  let sigmaM : ℝ := Annealed.sigmaBar M m
  let rho : ℝ := sigmaM / sigmaK
  let x : ℝ := sigmaK⁻¹ * Matrix.trace A.upperLeft
  let y : ℝ := sigmaK * Matrix.trace A.lowerRight
  obtain ⟨Lambda, hEll⟩ := cutoff_isEllipticFieldOn_cube M m omega (originCube 2 n)
  have htrpos := source_coarse_block_trace_pos M.nu_pos hEll
  have hsigmaK : 0 < sigmaK := by exact (Annealed.sigmaBar_characterization M K).1
  have hratioRaw := ASDExplicitGamma.Scalar.sigmaBar_structural_continuity M K (m - K)
    (sub_nonneg.mpr hKm)
  have hratio : 1 ≤ rho ∧ rho ≤ Real.rpow 3 (2 * M.gamma * (m - K : ℝ)) := by
    dsimp [rho, sigmaK, sigmaM]
    simpa [Int.add_sub_cancel] using hratioRaw
  have hx : 0 < x := by
    dsimp [x]
    exact mul_pos (inv_pos.mpr hsigmaK) htrpos.1
  have hy : 0 < y := by
    dsimp [y]
    exact mul_pos hsigmaK htrpos.2
  have hprod : 4 ≤ x * y := by
    dsimp [x, y, A]
    have hp := source_coarse_block_trace_product M.nu_pos hEll
    have hs := hsigmaK.ne'
    have hcancel : (sigmaK⁻¹ * Matrix.trace
        (coarseBlockMatrix (cubeSet (originCube 2 n))
          (Cutoff.coefficientCutoff M.nu m omega).toFun).upperLeft) *
        (sigmaK * Matrix.trace (coarseBlockMatrix (cubeSet (originCube 2 n))
          (Cutoff.coefficientCutoff M.nu m omega).toFun).lowerRight) =
        Matrix.trace (coarseBlockMatrix (cubeSet (originCube 2 n))
          (Cutoff.coefficientCutoff M.nu m omega).toFun).upperLeft *
        Matrix.trace (coarseBlockMatrix (cubeSet (originCube 2 n))
          (Cutoff.coefficientCutoff M.nu m omega).toFun).lowerRight := by
      field_simp [hs]
    rw [hcancel]
    exact hp
  have hT : 0 ≤ x + y - 4 := by
    change 0 ≤ traceDefect (cubeSet (originCube 2 n))
      (Cutoff.coefficientCutoff M.nu m omega).toFun sigmaK
    exact traceDefect_nonneg_of_ellipticFieldOn_triCube M.nu_pos hEll hsigmaK
  have hratioUpper : rho ≤ Real.rpow 3
      (2 * M.gamma * (m - K : ℝ)) := by
    simpa using hratio.2
  have hscalar := source_frame_trace_scalar_bound (h := (m - K : ℝ))
    hprod hT hratio.1 hratioUpper M.shellPrefix.gamma_pos.le
    (by exact_mod_cast (sub_nonneg.mpr hKm)) heta
  have hsigmaM : sigmaM ≠ 0 := by
    dsimp [sigmaM]
    exact (Annealed.sigmaBar M m).2.ne'
  have hxdiv : x / rho = sigmaM⁻¹ * Matrix.trace A.upperLeft := by
    dsimp [x, rho]
    field_simp [hsigmaK.ne', hsigmaM]
  have hydiv : rho * y = sigmaM * Matrix.trace A.lowerRight := by
    dsimp [rho, y]
    field_simp [hsigmaK.ne']
  have hnew : cutoffTraceDefect M m n omega = x / rho + rho * y - 4 := by
    change sigmaM⁻¹ * Matrix.trace A.upperLeft +
      sigmaM * Matrix.trace A.lowerRight - 4 = _
    rw [← hxdiv, ← hydiv]
  have hold : traceDefect (cubeSet (originCube 2 n))
      (Cutoff.coefficientCutoff M.nu m omega).toFun sigmaK = x + y - 4 := by
    dsimp [x, y, sigmaK, A]
    unfold traceDefect
    field_simp [hsigmaK.ne']
  rw [hnew]
  rw [hold]
  simpa [rho] using hscalar


end
end ASDExplicitGamma.Inverse
