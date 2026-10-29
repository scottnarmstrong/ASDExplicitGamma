module

public import ASDExplicitGamma.Native.OldSignedCellProjection
public import ASDExplicitGamma.Scalar.FullResponseHistory
public import ASDExplicitGamma.Scalar.InverseHistoryLambda
public import ASDExplicitGamma.Triadic.PlanarConstants
public import ASDExplicitGamma.Triadic.VectorHaar
public import ASDExplicitGamma.Variational.TraceDefect
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Tactic.Linarith

/-! Exact OLD signed-generator histories, source norms, and affine correctors. -/
@[expose] public section

namespace ASDExplicitGamma.Native

open Homogenization MeasureTheory Response Scalar Triadic Variational
open scoped ENNReal

noncomputable section

/-- The OLD planar positive-Haar coefficient is certified at `.304`; this is
the constant used in the signed-generator source and is independent of the
main `.319` boundary bill. -/
theorem old_signed_planarC1_le_304 : planarC1 ≤ (304 / 1000 : ℝ) := by
  have hs0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  have hsq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs : Real.sqrt 3 ≤ (26 / 15 : ℝ) := by nlinarith only [hsq, hs0]
  have hp : (157 / 50 : ℝ) ≤ Real.pi := by linarith only [Real.pi_gt_d2]
  have hp2 : (157 / 50 : ℝ) ^ 2 ≤ Real.pi ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hp 2
  have hf : (1 - 26 / 135 : ℝ) ≤ 1 - Real.sqrt 3 / 9 := by linarith only [hs]
  have hd : 0 < Real.pi ^ 2 * (1 - Real.sqrt 3 / 9) :=
    mul_pos (pow_pos Real.pi_pos _) (lt_of_lt_of_le (by norm_num) hf)
  have hdlo : (157 / 50 : ℝ) ^ 2 * (1 - 26 / 135) ≤
      Real.pi ^ 2 * (1 - Real.sqrt 3 / 9) :=
    mul_le_mul hp2 hf (by norm_num) (sq_nonneg Real.pi)
  have hnum : Real.sqrt 3 - 1 ≤
      (304 / 1000 : ℝ) ^ 2 * (Real.pi ^ 2 * (1 - Real.sqrt 3 / 9)) := by
    calc
      _ ≤ (26 / 15 : ℝ) - 1 := sub_le_sub_right hs 1
      _ ≤ (304 / 1000 : ℝ) ^ 2 * ((157 / 50) ^ 2 * (1 - 26 / 135)) := by norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left hdlo (sq_nonneg _)
  have hcap : planarC1 ^ 2 ≤ (304 / 1000 : ℝ) ^ 2 := by
    rw [planarC1_sq]
    exact (div_le_iff₀ hd).mpr hnum
  exact (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num)).mp hcap

/-- The discounted positive trace-defect history of the actual response field. -/
def oldSignedTraceHistory (Q : TriadicCube 2) (a : CoeffField 2) : ℝ≥0∞ :=
  ENNReal.ofReal (1 - Scalar.inverseHistoryDiscount) *
    ∑' j : ℕ, ENNReal.ofReal (Scalar.inverseHistoryDiscount ^ j *
      descendantsAverage Q j (fun R => traceDefect (openCubeSet R) a 1))

/-- The exact quarter-discounted inverse-response history. -/
def oldSignedInverseHistory (Q : TriadicCube 2) (a : CoeffField 2) : ℝ :=
  lemmaVInverseHistory Q a ((3 : ℝ) ^ (1 / 4 : ℝ))

/-- The extended complete full-response history, converted to its real value. -/
def oldSignedResponseHistory (Q : TriadicCube 2) (a : CoeffField 2) : ℝ :=
  (completeFullResponseHistory Q a).toReal

/-- The history controlling the affine first corrector and reciprocal bounds. -/
def oldSignedCorrectorHistory (Q : TriadicCube 2) (a : CoeffField 2) : ℝ :=
  (1 + Scalar.inverseHistoryDiscount) * oldSignedResponseHistory Q a *
    (oldSignedTraceHistory Q a).toReal

/-- The four-component positive Haar norm of a doubled source field. -/
def oldSignedBlockPositiveNorm (Q : TriadicCube 2)
    (F : Vec 2 → BlockVec 2) : ℝ :=
  Real.sqrt ((vectorPositiveHaarNorm Q (fun x => (F x).1) ^ 2) +
    (vectorPositiveHaarNorm Q (fun x => (F x).2) ^ 2))

/-- The four-component weak Haar norm of a doubled source field. -/
def oldSignedBlockWeakNorm (Q : TriadicCube 2)
    (F : Vec 2 → BlockVec 2) : ℝ :=
  Real.sqrt ((vectorWeakHaarNorm Q (fun x => (F x).1) ^ 2) +
    (vectorWeakHaarNorm Q (fun x => (F x).2) ^ 2))

/-- The four-component affine mean of a doubled L² source. -/
def oldSignedBlockMean (Q : TriadicCube 2)
    (F : Vec 2 → BlockVec 2) : BlockVec 2 :=
  ((fun i => cubeAverage Q (fun x => (F x).1 i)),
    (fun i => cubeAverage Q (fun x => (F x).2 i)) )

end

end ASDExplicitGamma.Native
