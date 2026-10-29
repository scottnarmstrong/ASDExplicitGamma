module

public import ASDExplicitGamma.Main.HotCovFlatError
public import ASDExplicitGamma.Main.HotFlatProfile
public import ASDExplicitGamma.Main.FlatFieldSourceCaps
public import ASDExplicitGamma.Scalar.OldHessianTrialFrobeniusMesh

/-! MA-E-COVARIANCE, step 10: the covariance errors `e_±` at the actual shell
length, in the literal form of MA-FLAT-FIELD. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Native ASDExplicitGamma.Scalar
  ASDExplicitGamma.Triadic ASDExplicitGamma.Gaussian

noncomputable section

private theorem hotCov_err_cap_core (Q : TriadicCube 2) (depth : ℕ) (b B0 : ℝ)
    (L : {l : ℝ // 0 < l}) (plus : Bool)
    (hL : cubeScaleFactor Q / (3 : ℝ) ^ depth * (3 : ℝ) ^ 6 ≤ L.1)
    (hB : oldSignedFlatBoundaryEnergy Q b L ≤ B0) (op : ℝ) (hop0 : 0 ≤ op)
    (hop : descendantsAverage Q depth (fun U =>
      oldSignedFlatOscillationSize Q U b L plus ^ 2) ≤ op ^ 2) :
    Real.sqrt (descendantsAverage Q depth (fun U => hotCovErrCellEnergy Q U b L plus)) ≤
      Real.sqrt (b ^ 2 * B0 / 2) +
        (319 / 1000) * Real.sqrt ((156 / 5) * mainA2 (b ^ 2)) * op := by
  have h := hotCov_err_frobenius Q depth b L plus
  refine h.trans (add_le_add ?_ ?_)
  · rw [← Real.sqrt_sq_eq_abs b, ← Real.sqrt_mul (sq_nonneg b)]
    apply Real.sqrt_le_sqrt
    have : oldSignedFlatBoundaryEnergy Q b L / 2 ≤ B0 / 2 := by linarith
    nlinarith [sq_nonneg b, mul_le_mul_of_nonneg_left this (sq_nonneg b)]
  · set r := cubeScaleFactor Q / (3 : ℝ) ^ depth with hr
    have hrpos : 0 < r := div_pos (Triadic.cubeScaleFactor_pos' Q) (by positivity)
    have hscale := hot_flat_scale_arith r b L hrpos hL
    have hinv := old_hessian_inverse_pi_le_319
    have e1 : r / Real.pi * Real.sqrt (mainFlatSigmaSq b L) *
        Real.sqrt (descendantsAverage Q depth (fun U =>
          oldSignedFlatOscillationSize Q U b L plus ^ 2)) =
        (1 / Real.pi) * (Real.sqrt (r ^ 2 * mainFlatSigmaSq b L) *
          Real.sqrt (descendantsAverage Q depth (fun U =>
            oldSignedFlatOscillationSize Q U b L plus ^ 2))) := by
      rw [Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hrpos.le]
      ring
    rw [e1]
    have hsq : Real.sqrt (r ^ 2 * mainFlatSigmaSq b L) ≤ Real.sqrt ((156 / 5) * mainA2 (b ^ 2)) := by
      apply Real.sqrt_le_sqrt
      have : (31.2 : ℝ) = 156 / 5 := by norm_num
      rw [← this]
      exact hscale
    have hop' : Real.sqrt (descendantsAverage Q depth (fun U =>
        oldSignedFlatOscillationSize Q U b L plus ^ 2)) ≤ op := by
      calc _ ≤ Real.sqrt (op ^ 2) := Real.sqrt_le_sqrt hop
        _ = op := Real.sqrt_sq hop0
    have hprod : Real.sqrt (r ^ 2 * mainFlatSigmaSq b L) *
        Real.sqrt (descendantsAverage Q depth (fun U =>
          oldSignedFlatOscillationSize Q U b L plus ^ 2)) ≤
        Real.sqrt ((156 / 5) * mainA2 (b ^ 2)) * op :=
      mul_le_mul hsq hop' (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    calc (1 / Real.pi) * (Real.sqrt (r ^ 2 * mainFlatSigmaSq b L) *
          Real.sqrt (descendantsAverage Q depth (fun U =>
            oldSignedFlatOscillationSize Q U b L plus ^ 2)))
        ≤ (319 / 1000) * (Real.sqrt ((156 / 5) * mainA2 (b ^ 2)) * op) :=
          mul_le_mul hinv hprod (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
            (by norm_num)
      _ = _ := by ring

/-- The plus covariance error, cell-averaged: `e_+` of MA-FLAT-FIELD. -/
theorem hotCov_err_cap_plus (Q : TriadicCube 2) (depth : ℕ) (b B0 : ℝ)
    (L : {l : ℝ // 0 < l})
    (hL : cubeScaleFactor Q / (3 : ℝ) ^ depth * (3 : ℝ) ^ 6 ≤ L.1)
    (hB : oldSignedFlatBoundaryEnergy Q b L ≤ B0) :
    Real.sqrt (descendantsAverage Q depth (fun U => hotCovErrCellEnergy Q U b L true)) ≤
      mainFlatBoundaryEPlus (b ^ 2) B0 := by
  have h := hotCov_err_cap_core Q depth b B0 L true hL hB (mainOp (b ^ 2))
    (by unfold mainOp; positivity) (main_hot_flatPlus_descendant_average_le_mainOp_sq Q depth b L hL)
  unfold mainFlatBoundaryEPlus
  exact h

/-- The minus covariance error, cell-averaged: `e_-` of MA-FLAT-FIELD. -/
theorem hotCov_err_cap_minus (Q : TriadicCube 2) (depth : ℕ) (b B0 : ℝ)
    (L : {l : ℝ // 0 < l})
    (hL : cubeScaleFactor Q / (3 : ℝ) ^ depth * (3 : ℝ) ^ 6 ≤ L.1)
    (hB : oldSignedFlatBoundaryEnergy Q b L ≤ B0) :
    Real.sqrt (descendantsAverage Q depth (fun U => hotCovErrCellEnergy Q U b L false)) ≤
      mainFlatBoundaryEMinus (b ^ 2) B0 := by
  have h := hotCov_err_cap_core Q depth b B0 L false hL hB (mainOm (b ^ 2))
    (by unfold mainOm; positivity) (main_hot_flatMinus_descendant_average_le_mainOm_sq Q depth b L hL)
  unfold mainFlatBoundaryEMinus
  exact h

end

end ASDExplicitGamma.Main
