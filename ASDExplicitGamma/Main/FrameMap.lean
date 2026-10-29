module

public import ASDExplicitGamma.Main.FrameAlgebra
public import ASDExplicitGamma.Scalar.StructuralContinuity
public import ASDExplicitGamma.Variational.AdapterDuality
public import ASDExplicitGamma.Numerics.AllOrder.Allocations

/-! Pathwise true-frame restoration and its completed-law mean adapter. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization Algsuperdiff.Section3 MeasureTheory
open ASDExplicitGamma.Variational

private theorem main_frame_ratio_error {rho gamma h : ℝ}
    (hrho : 1 ≤ rho)
    (hrhoUpper : rho ≤ Real.rpow 3 (2 * gamma * (h - 1)))
    (hgamma : 0 ≤ gamma) (hh : 1 ≤ h) :
    0 ≤ 1 - rho⁻¹ ∧ 1 - rho⁻¹ ≤ (11 / 5 : ℝ) * gamma * h := by
  have hrhoPos : 0 < rho := lt_of_lt_of_le zero_lt_one hrho
  have ha : 0 ≤ 2 * gamma * (h - 1) := by positivity
  have hRpos : 0 < Real.rpow 3 (2 * gamma * (h - 1)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hRinv : (Real.rpow 3 (2 * gamma * (h - 1)))⁻¹ =
      Real.exp (-(2 * gamma * (h - 1) * Real.log 3)) := by
    calc
      _ = Real.rpow 3 (-(2 * gamma * (h - 1))) :=
        (Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3) _).symm
      _ = Real.exp (Real.log 3 * (-(2 * gamma * (h - 1)))) :=
        Real.rpow_def_of_pos (by norm_num) _
      _ = _ := by congr 1; ring
  have hinv : (Real.rpow 3 (2 * gamma * (h - 1)))⁻¹ ≤ rho⁻¹ :=
    (inv_le_inv₀ hRpos hrhoPos).2 hrhoUpper
  have hlog : Real.log 3 ≤ 11 / 10 := ASDExplicitGamma.Numerics.Scalar.log_three_small.2.le
  have hlogNonneg : 0 ≤ Real.log 3 := (Real.log_pos (by norm_num)).le
  have hexp : 1 - Real.exp (-(2 * gamma * (h - 1) * Real.log 3)) ≤
      2 * gamma * (h - 1) * Real.log 3 := by
    have := Real.add_one_le_exp (-(2 * gamma * (h - 1) * Real.log 3))
    linarith
  constructor
  · exact sub_nonneg.mpr (inv_le_one_of_one_le₀ hrho)
  · calc
      1 - rho⁻¹ ≤ 1 - (Real.rpow 3 (2 * gamma * (h - 1)))⁻¹ := by linarith
      _ = 1 - Real.exp (-(2 * gamma * (h - 1) * Real.log 3)) := by rw [hRinv]
      _ ≤ 2 * gamma * (h - 1) * Real.log 3 := hexp
      _ ≤ (11 / 5 : ℝ) * gamma * h := by nlinarith [hlog, hlogNonneg, hgamma, hh]

/-- The scalar two-block frame inequality, including the source's simplified
`(1 + eta)` bound. The product condition is discharged for coarse responses
below from ellipticity and nonnegative trace defects. -/
theorem main_frame_trace_scalar_bound {x y rho gamma h eta : ℝ}
    (hprod : 4 ≤ x * y)
    (hT : 0 ≤ x + y - 4) (hrho : 1 ≤ rho)
    (hrhoUpper : rho ≤ Real.rpow 3 (2 * gamma * (h - 1)))
    (hgamma : 0 ≤ gamma) (hh : 1 ≤ h) (heta : 0 < eta) :
    x / rho + rho * y - 4 ≤
      rho * ((1 + eta) * (x + y - 4) +
        8 * (1 + 1 / eta) * ((11 / 10 : ℝ) * gamma * h) ^ 2) := by
  let T : ℝ := x + y - 4
  let c : ℝ := (rho + rho⁻¹) / 2
  let d : ℝ := (rho - rho⁻¹) / 2
  let s : ℝ := Real.sqrt (8 * T)
  have hrhoPos : 0 < rho := lt_of_lt_of_le zero_lt_one hrho
  have hinv_le : rho⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hrho
  have hdNonneg : 0 ≤ d := by dsimp [d]; linarith
  have hT' : 0 ≤ T := by simpa [T] using hT
  have hrad : 0 ≤ T * (T + 8) := mul_nonneg hT' (by linarith)
  have hsNonneg : 0 ≤ s := Real.sqrt_nonneg _
  have hsSq : s ^ 2 = 8 * T := by
    dsimp [s]
    exact Real.sq_sqrt (by positivity)
  have hdiffSq : (y - x) ^ 2 ≤ T * (T + 8) := by
    have hid : T * (T + 8) - (y - x) ^ 2 = 4 * (x * y - 4) := by
      dsimp [T]
      ring
    nlinarith [hid, hprod]
  have hdiffAbs : |y - x| ≤ Real.sqrt (T * (T + 8)) := by
    apply (Real.le_sqrt (abs_nonneg _) hrad).2
    rw [sq_abs]
    exact hdiffSq
  have hdiff : y - x ≤ Real.sqrt (T * (T + 8)) := le_trans (le_abs_self _) hdiffAbs
  have hroot : Real.sqrt (T * (T + 8)) ≤ T + s := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · nlinarith [hsSq, mul_nonneg hT' hsNonneg]
  have hYoung : d * s ≤ eta * rho * T + 2 * d ^ 2 / (eta * rho) := by
    have hetaRho : 0 < eta * rho := mul_pos heta hrhoPos
    have hidentity :
        8 * ((eta * rho) ^ 2 * T - eta * rho * d * s + 2 * d ^ 2) =
          (eta * rho * s - 4 * d) ^ 2 := by
      calc
        _ = (eta * rho) ^ 2 * (8 * T) - 8 * eta * rho * d * s + 16 * d ^ 2 := by ring
        _ = (eta * rho) ^ 2 * s ^ 2 - 8 * eta * rho * d * s + 16 * d ^ 2 := by rw [hsSq]
        _ = _ := by ring
    have hpoly : 0 ≤ (eta * rho) ^ 2 * T - eta * rho * d * s + 2 * d ^ 2 := by
      nlinarith [sq_nonneg (eta * rho * s - 4 * d), hidentity]
    have hcross : (d * s - eta * rho * T) * (eta * rho) ≤ 2 * d ^ 2 := by
      nlinarith [hpoly]
    have hdiv : d * s - eta * rho * T ≤ 2 * d ^ 2 / (eta * rho) :=
      (le_div_iff₀ hetaRho).2 hcross
    linarith
  have hfactor : d = (rho - 1) * ((rho + 1) / (2 * rho)) := by
    dsimp [d]
    field_simp [hrhoPos.ne']
    ring
  have hfactorLe : (rho + 1) / (2 * rho) ≤ 1 := by
    apply (div_le_iff₀ (by positivity)).2
    nlinarith
  have hdLe : d ≤ rho - 1 := by
    rw [hfactor]
    calc
      (rho - 1) * ((rho + 1) / (2 * rho)) ≤ (rho - 1) * 1 :=
        mul_le_mul_of_nonneg_left hfactorLe (by linarith)
      _ = rho - 1 := by ring
  have hdSq : d ^ 2 ≤ (rho - 1) ^ 2 :=
    (sq_le_sq₀ hdNonneg (by linarith)).2 hdLe
  have hcd : c + d = rho := by
    dsimp [c, d]
    ring
  have hfourC : 4 * (c - 1) = 2 * (rho - 1) ^ 2 / rho := by
    dsimp [c]
    field_simp [hrhoPos.ne']
    ring
  have hrepr : x / rho + rho * y - 4 = c * T + d * (y - x) + 4 * (c - 1) := by
    dsimp [c, d, T]
    field_simp [hrhoPos.ne']
    ring
  have hlin : x / rho + rho * y - 4 ≤
      rho * T + eta * rho * T + 4 * (c - 1) + 2 * d ^ 2 / (eta * rho) := by
    rw [hrepr]
    have hdifmul := mul_le_mul_of_nonneg_left (hdiff.trans hroot) hdNonneg
    calc
      c * T + d * (y - x) + 4 * (c - 1) ≤
          c * T + d * (T + s) + 4 * (c - 1) := by linarith
      _ = (c + d) * T + d * s + 4 * (c - 1) := by ring
      _ = rho * T + d * s + 4 * (c - 1) := by rw [hcd]
      _ ≤ rho * T + eta * rho * T + 4 * (c - 1) +
            2 * d ^ 2 / (eta * rho) := by linarith
  have herror := (main_frame_ratio_error hrho hrhoUpper hgamma hh)
  have hdeltaSq : (1 - rho⁻¹) ^ 2 ≤ ((11 / 5 : ℝ) * gamma * h) ^ 2 :=
    (sq_le_sq₀ herror.1 (by positivity)).2 herror.2
  have htail : 4 * (c - 1) + 2 * d ^ 2 / (eta * rho) ≤
      2 * (1 + 1 / eta) * (rho - 1) ^ 2 / rho := by
    rw [hfourC]
    have hterm : 2 * d ^ 2 / (eta * rho) ≤ 2 * (rho - 1) ^ 2 / (eta * rho) := by
      calc
        2 * d ^ 2 / (eta * rho) = (2 / (eta * rho)) * d ^ 2 := by ring
        _ ≤ (2 / (eta * rho)) * (rho - 1) ^ 2 :=
          mul_le_mul_of_nonneg_left hdSq (by positivity)
        _ = 2 * (rho - 1) ^ 2 / (eta * rho) := by ring
    have hsum :
        2 * (rho - 1) ^ 2 / rho + 2 * (rho - 1) ^ 2 / (eta * rho) =
          2 * (1 + 1 / eta) * (rho - 1) ^ 2 / rho := by ring
    rw [← hsum]
    nlinarith [hterm]
  have hratioTerm :
      2 * (1 + 1 / eta) * (rho - 1) ^ 2 / rho =
        2 * rho * (1 + 1 / eta) * (1 - rho⁻¹) ^ 2 := by
    field_simp [hrhoPos.ne']
  have htail' : 4 * (c - 1) + 2 * d ^ 2 / (eta * rho) ≤
      8 * rho * (1 + 1 / eta) * ((11 / 10 : ℝ) * gamma * h) ^ 2 := by
    have hscale' : 0 ≤ 2 * rho * (1 + 1 / eta) := by positivity
    calc
      _ ≤ 2 * (1 + 1 / eta) * (rho - 1) ^ 2 / rho := htail
      _ = 2 * rho * (1 + 1 / eta) * (1 - rho⁻¹) ^ 2 := hratioTerm
      _ ≤ 2 * rho * (1 + 1 / eta) * ((11 / 5 : ℝ) * gamma * h) ^ 2 :=
        mul_le_mul_of_nonneg_left hdeltaSq hscale'
      _ = 8 * rho * (1 + 1 / eta) * ((11 / 10 : ℝ) * gamma * h) ^ 2 := by ring
  calc
    _ ≤ rho * T + eta * rho * T + 4 * (c - 1) + 2 * d ^ 2 / (eta * rho) := hlin
    _ ≤ rho * ((1 + eta) * T +
          8 * (1 + 1 / eta) * ((11 / 10 : ℝ) * gamma * h) ^ 2) := by
      calc
        _ = (rho * T + eta * rho * T) +
            (4 * (c - 1) + 2 * d ^ 2 / (eta * rho)) := by ring
        _ ≤ rho * T + eta * rho * T +
            rho * (8 * (1 + 1 / eta) * ((11 / 10 : ℝ) * gamma * h) ^ 2) := by
          linarith [htail']
        _ = _ := by ring

/-- The two block traces of an elliptic coarse response are strictly positive. -/
private theorem main_coarse_block_trace_pos {Q : TriadicCube 2} {nu Lambda : ℝ}
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
private theorem main_coarse_block_trace_product {Q : TriadicCube 2} {nu Lambda : ℝ}
    {a : CoeffField 2} (hnu : 0 < nu)
    (hEll : IsEllipticFieldOn nu Lambda (cubeSet Q) a) :
    4 ≤ Matrix.trace (coarseBlockMatrix (cubeSet Q) a).upperLeft *
      Matrix.trace (coarseBlockMatrix (cubeSet Q) a).lowerRight := by
  have hpos := main_coarse_block_trace_pos hnu hEll
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
theorem main_cutoff_pathwise_frame_map (M : ABKModel 2) (K m n : ℤ)
    (omega : Cutoff.CutoffSample 2) (hKm : K ≤ m) (eta : ℝ) (heta : 0 < eta) :
    cutoffTraceDefect M m n omega ≤
      ((Annealed.sigmaBar M m : ℝ) / (Annealed.sigmaBar M K : ℝ)) *
        ((1 + eta) * traceDefect (cubeSet (originCube 2 n))
            (Cutoff.coefficientCutoff M.nu m omega).toFun
            (Annealed.sigmaBar M K : ℝ) +
          8 * (1 + 1 / eta) *
            ((11 / 10 : ℝ) * M.gamma * ((m - K : ℝ) + 1)) ^ 2) := by
  let A := coarseBlockMatrix (cubeSet (originCube 2 n))
    (Cutoff.coefficientCutoff M.nu m omega).toFun
  let sigmaK : ℝ := Annealed.sigmaBar M K
  let sigmaM : ℝ := Annealed.sigmaBar M m
  let rho : ℝ := sigmaM / sigmaK
  let x : ℝ := sigmaK⁻¹ * Matrix.trace A.upperLeft
  let y : ℝ := sigmaK * Matrix.trace A.lowerRight
  obtain ⟨Lambda, hEll⟩ := cutoff_isEllipticFieldOn_cube M m omega (originCube 2 n)
  have htrpos := main_coarse_block_trace_pos M.nu_pos hEll
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
    have hp := main_coarse_block_trace_product M.nu_pos hEll
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
      (2 * M.gamma * ((m - K : ℝ) + 1 - 1)) := by
    simpa using hratio.2
  have hscalar := main_frame_trace_scalar_bound (h := (m - K : ℝ) + 1)
    hprod hT hratio.1 hratioUpper M.shellPrefix.gamma_pos.le
    (by
      have hg : 0 ≤ (m - K : ℝ) := by exact_mod_cast (sub_nonneg.mpr hKm)
      change 1 ≤ (m - K : ℝ) + 1
      linarith) heta
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

end ASDExplicitGamma.Main
