module

public import ASDExplicitGamma.Variational.TrueFrame
public import Mathlib.Tactic.FieldSimp

/-! Completed-law frame restoration, separated from the scalar ratio theorem. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization Homogenization.Book Algsuperdiff.Section3 MeasureTheory
open ASDExplicitGamma.Variational

/-- The two scalar blocks in the true frame determine the trace in every
positive deterministic frame. This identity concerns a completed law. -/
theorem main_completed_trace_scalar_formula (M : ABKModel 2) (k n : ℤ) :
    ∃ alpha beta : ℝ, 1 ≤ alpha ∧ 1 ≤ beta ∧ ∀ sigma : ℝ, 0 < sigma →
      (∫ a : RegCoeffField 2, traceDefect (cubeSet (originCube 2 n)) a.toFun sigma
        ∂(Cutoff.coefficientCutoffLaw M k)) =
        2 * ((Annealed.sigmaBar M k : ℝ) / sigma) * alpha +
          2 * (sigma / (Annealed.sigmaBar M k : ℝ)) * beta - 4 := by
  obtain ⟨alpha, beta, ha, hb, hmean⟩ := Variational.exists_trueFrame_mean_scalars M k n
  have hm := hmean 0
  rw [translateSet_zero] at hm
  have hul := congrArg BlockMat.upperLeft hm
  have hlr := congrArg BlockMat.lowerRight hm
  have hs : (Annealed.sigmaBar M k : ℝ) ≠ 0 := (Annealed.sigmaBar M k).2.ne'
  refine ⟨alpha, beta, ha, hb, ?_⟩
  intro sigma hsigma
  rw [Variational.integral_traceDefect_eq_annealed_trace]
  have htrul := congrArg Matrix.trace hul
  have htrlr := congrArg Matrix.trace hlr
  simp only [frameMatrix, Ch02.blockDiag, Matrix.trace_smul, Matrix.trace_one,
    Fintype.card_fin, Nat.cast_ofNat, smul_eq_mul] at htrul htrlr
  have haeq : Matrix.trace
      (Ch04.annealedBlockMatrix (Cutoff.coefficientCutoffLaw M k)
        (cubeSet (originCube 2 n))).upperLeft =
      2 * (Annealed.sigmaBar M k : ℝ) * alpha := by
    calc
      _ = (Annealed.sigmaBar M k : ℝ) *
          ((Annealed.sigmaBar M k : ℝ)⁻¹ * Matrix.trace
            (Ch04.annealedBlockMatrix (Cutoff.coefficientCutoffLaw M k)
              (cubeSet (originCube 2 n))).upperLeft) := by field_simp
      _ = _ := by rw [htrul]; ring
  rw [haeq]
  have hbeq : Matrix.trace
      (Ch04.annealedBlockMatrix (Cutoff.coefficientCutoffLaw M k)
        (cubeSet (originCube 2 n))).lowerRight =
      2 * (Annealed.sigmaBar M k : ℝ)⁻¹ * beta := by
    calc
      _ = (Annealed.sigmaBar M k : ℝ)⁻¹ *
          ((Annealed.sigmaBar M k : ℝ) * Matrix.trace
            (Ch04.annealedBlockMatrix (Cutoff.coefficientCutoffLaw M k)
              (cubeSet (originCube 2 n))).lowerRight) := by field_simp
      _ = _ := by rw [htrlr]; ring
  rw [hbeq]
  simp only [div_eq_mul_inv]
  ring

/-- Scalar restoration of a positive completed mean. No partial-insertion
law or history enters this algebraic estimate. -/
theorem main_frame_scalar_return (alpha beta r : ℝ) (ha : 1 ≤ alpha)
    (hb : 1 ≤ beta) (hr : 1 ≤ r) :
    0 ≤ 2 * r * alpha + 2 / r * beta - 4 ∧
    2 * alpha + 2 * beta - 4 ≤ r * (2 * r * alpha + 2 / r * beta - 4) := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hid : r * (2 * r * alpha + 2 / r * beta - 4) -
      (2 * alpha + 2 * beta - 4) =
      2 * (r ^ 2 - 1) * (alpha - 1) + 2 * (r - 1) ^ 2 := by
    field_simp
    ring
  have hdiff : 0 ≤ r * (2 * r * alpha + 2 / r * beta - 4) -
      (2 * alpha + 2 * beta - 4) := by
    rw [hid]
    exact add_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by nlinarith)) (sub_nonneg.mpr ha))
      (mul_nonneg (by norm_num) (sq_nonneg _))
  have hnew : 0 ≤ 2 * alpha + 2 * beta - 4 := by linarith
  have hold : 0 ≤ r * (2 * r * alpha + 2 / r * beta - 4) := by linarith
  exact ⟨(mul_nonneg_iff_of_pos_left hrpos).mp hold, by linarith⟩

/-- Completed-law restoration from the structural scalar ratio. The ratio
premises are the separate scalar-continuity input, not a partial-law estimate. -/
theorem main_completed_frame_return_of_ratio (M : ABKModel 2) (k n : ℤ)
    (oldFrame R : ℝ) (hold : 0 < oldFrame)
    (hr : 1 ≤ (Annealed.sigmaBar M k : ℝ) / oldFrame)
    (hR : (Annealed.sigmaBar M k : ℝ) / oldFrame ≤ R) :
    (∫ a : RegCoeffField 2,
      traceDefect (cubeSet (originCube 2 n)) a.toFun (Annealed.sigmaBar M k : ℝ)
      ∂(Cutoff.coefficientCutoffLaw M k)) ≤
    R * (∫ a : RegCoeffField 2,
      traceDefect (cubeSet (originCube 2 n)) a.toFun oldFrame
      ∂(Cutoff.coefficientCutoffLaw M k)) := by
  obtain ⟨alpha, beta, ha, hb, hformula⟩ := main_completed_trace_scalar_formula M k n
  rw [hformula _ (Annealed.sigmaBar M k).2, hformula _ hold]
  have hs : (Annealed.sigmaBar M k : ℝ) ≠ 0 := (Annealed.sigmaBar M k).2.ne'
  have hid : oldFrame / (Annealed.sigmaBar M k : ℝ) =
      ((Annealed.sigmaBar M k : ℝ) / oldFrame)⁻¹ := by
    simp only [inv_div]
  simp only [div_self hs, mul_one]
  rw [hid]
  have hbound := main_frame_scalar_return alpha beta
    ((Annealed.sigmaBar M k : ℝ) / oldFrame) ha hb hr
  simp only [div_eq_mul_inv] at hbound
  exact hbound.2.trans (mul_le_mul_of_nonneg_right hR hbound.1)

end ASDExplicitGamma.Main
