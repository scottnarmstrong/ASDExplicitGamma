module

public import ASDExplicitGamma.Main.FrameMap

/-! True-frame restoration for an arbitrary fixed elliptic coefficient. -/
@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization Algsuperdiff.Section3 ASDExplicitGamma.Variational

/-- Coarse duality makes the product of the two unframed block traces at least
four. The frame parameter used to test nonnegativity is chosen to balance them. -/
private theorem raw_coarse_block_trace_product {Q : TriadicCube 2} {nu Lambda : ℝ}
    {a : CoeffField 2} (hnu : 0 < nu)
    (ha : IsEllipticFieldOn nu Lambda (cubeSet Q) a) :
    4 ≤ Matrix.trace (coarseBlockMatrix (cubeSet Q) a).upperLeft *
      Matrix.trace (coarseBlockMatrix (cubeSet Q) a).lowerRight := by
  have hA : (toFullBlockMat (coarseBlockMatrix (cubeSet Q) a)).PosDef :=
    coarseBlockMatrix_posDef hnu ha
  have hUL0 : 0 < (coarseBlockMatrix (cubeSet Q) a).upperLeft 0 0 := by
    have h := hA.diag_pos (i := Sum.inl (0 : Fin 2))
    simpa [toFullBlockMat] using h
  have hUL1 : 0 < (coarseBlockMatrix (cubeSet Q) a).upperLeft 1 1 := by
    have h := hA.diag_pos (i := Sum.inl (1 : Fin 2))
    simpa [toFullBlockMat] using h
  have hLR0 : 0 < (coarseBlockMatrix (cubeSet Q) a).lowerRight 0 0 := by
    have h := hA.diag_pos (i := Sum.inr (0 : Fin 2))
    simpa [toFullBlockMat] using h
  have hLR1 : 0 < (coarseBlockMatrix (cubeSet Q) a).lowerRight 1 1 := by
    have h := hA.diag_pos (i := Sum.inr (1 : Fin 2))
    simpa [toFullBlockMat] using h
  have hUL : 0 < Matrix.trace (coarseBlockMatrix (cubeSet Q) a).upperLeft := by
    simpa [Matrix.trace, Fin.sum_univ_two] using add_pos hUL0 hUL1
  have hLR : 0 < Matrix.trace (coarseBlockMatrix (cubeSet Q) a).lowerRight := by
    simpa [Matrix.trace, Fin.sum_univ_two] using add_pos hLR0 hLR1
  let sigma : ℝ := 2 / Matrix.trace (coarseBlockMatrix (cubeSet Q) a).lowerRight
  have hsigma : 0 < sigma := by
    dsimp [sigma]
    exact div_pos (by norm_num) hLR
  have hdef := traceDefect_nonneg_of_ellipticFieldOn_triCube hnu ha hsigma
  have hinv : sigma⁻¹ = Matrix.trace (coarseBlockMatrix (cubeSet Q) a).lowerRight / 2 := by
    dsimp [sigma]
    field_simp [hLR.ne']
  have hscale : sigma * Matrix.trace (coarseBlockMatrix (cubeSet Q) a).lowerRight = 2 := by
    dsimp [sigma]
    field_simp [hLR.ne']
  change 0 ≤ sigma⁻¹ * Matrix.trace (coarseBlockMatrix (cubeSet Q) a).upperLeft +
    sigma * Matrix.trace (coarseBlockMatrix (cubeSet Q) a).lowerRight - 4 at hdef
  rw [hinv, hscale] at hdef
  nlinarith

/-- Restoring the scalar frame of any fixed elliptic coefficient from frame
`K` to completed label `m` costs exactly the source Young term. This applies
pointwise to each deterministic attenuation in a raw-trace band. -/
theorem raw_trace_defect_frame_map
    (M : ABKModel 2) (K m : ℤ) (Q : TriadicCube 2)
    (a : CoeffField 2) (Lambda : ℝ)
    (ha : IsEllipticFieldOn M.nu Lambda (cubeSet Q) a)
    (hKm : K ≤ m) (eta : ℝ) (heta : 0 < eta) :
    traceDefect (cubeSet Q) a (Annealed.sigmaBar M m : ℝ) ≤
      ((Annealed.sigmaBar M m : ℝ) / (Annealed.sigmaBar M K : ℝ)) *
        ((1 + eta) * traceDefect (cubeSet Q) a (Annealed.sigmaBar M K : ℝ) +
          8 * (1 + 1 / eta) *
            ((11 / 10 : ℝ) * M.gamma * ((m - K : ℝ) + 1)) ^ 2) := by
  let A := coarseBlockMatrix (cubeSet Q) a
  let sigmaK : ℝ := Annealed.sigmaBar M K
  let sigmaM : ℝ := Annealed.sigmaBar M m
  let rho : ℝ := sigmaM / sigmaK
  let x : ℝ := sigmaK⁻¹ * Matrix.trace A.upperLeft
  let y : ℝ := sigmaK * Matrix.trace A.lowerRight
  have htrpos : 0 < Matrix.trace A.upperLeft ∧ 0 < Matrix.trace A.lowerRight := by
    have hpos : (toFullBlockMat A).PosDef := coarseBlockMatrix_posDef M.nu_pos ha
    constructor
    · have h0 : 0 < A.upperLeft 0 0 := by
        have h := hpos.diag_pos (i := Sum.inl (0 : Fin 2))
        simpa [toFullBlockMat, A] using h
      have h1 : 0 < A.upperLeft 1 1 := by
        have h := hpos.diag_pos (i := Sum.inl (1 : Fin 2))
        simpa [toFullBlockMat, A] using h
      simpa [A, Matrix.trace, Fin.sum_univ_two] using add_pos h0 h1
    · have h0 : 0 < A.lowerRight 0 0 := by
        have h := hpos.diag_pos (i := Sum.inr (0 : Fin 2))
        simpa [toFullBlockMat, A] using h
      have h1 : 0 < A.lowerRight 1 1 := by
        have h := hpos.diag_pos (i := Sum.inr (1 : Fin 2))
        simpa [toFullBlockMat, A] using h
      simpa [A, Matrix.trace, Fin.sum_univ_two] using add_pos h0 h1
  have hsigmaK : 0 < sigmaK := (Annealed.sigmaBar_characterization M K).1
  have hx : 0 < x := by
    dsimp [x]
    exact mul_pos (inv_pos.mpr hsigmaK) htrpos.1
  have hy : 0 < y := by
    dsimp [y]
    exact mul_pos hsigmaK htrpos.2
  have hratioRaw := ASDExplicitGamma.Scalar.sigmaBar_structural_continuity M K (m - K)
    (sub_nonneg.mpr hKm)
  have hratio : 1 ≤ rho ∧ rho ≤ Real.rpow 3 (2 * M.gamma * (m - K : ℝ)) := by
    dsimp [rho, sigmaK, sigmaM]
    simpa [Int.add_sub_cancel] using hratioRaw
  have hprod : 4 ≤ x * y := by
    dsimp [x, y, A]
    have hp := raw_coarse_block_trace_product M.nu_pos ha
    have hcancel :
        (sigmaK⁻¹ * Matrix.trace (coarseBlockMatrix (cubeSet Q) a).upperLeft) *
          (sigmaK * Matrix.trace (coarseBlockMatrix (cubeSet Q) a).lowerRight) =
        Matrix.trace (coarseBlockMatrix (cubeSet Q) a).upperLeft *
          Matrix.trace (coarseBlockMatrix (cubeSet Q) a).lowerRight := by
      field_simp [hsigmaK.ne']
    rw [hcancel]
    exact hp
  have hT : 0 ≤ x + y - 4 := by
    change 0 ≤ traceDefect (cubeSet Q) a sigmaK
    exact traceDefect_nonneg_of_ellipticFieldOn_triCube M.nu_pos ha hsigmaK
  have hratioUpper : rho ≤ Real.rpow 3
      (2 * M.gamma * ((m - K : ℝ) + 1 - 1)) := by
    simpa using hratio.2
  have hscalar := ASDExplicitGamma.Main.main_frame_trace_scalar_bound
    (h := (m - K : ℝ) + 1) hprod hT hratio.1 hratioUpper
    M.shellPrefix.gamma_pos.le
    (by
      have hg : 0 ≤ (m - K : ℝ) := by exact_mod_cast (sub_nonneg.mpr hKm)
      change 1 ≤ (m - K : ℝ) + 1
      linarith)
    heta
  have hsigmaM : sigmaM ≠ 0 := (Annealed.sigmaBar_characterization M m).1.ne'
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
    dsimp [x, y, A]
    unfold traceDefect
    field_simp [hsigmaK.ne']
  rw [hnew, hold]
  simpa [rho] using hscalar

end ASDExplicitGamma.Inverse
