module

public import ASDExplicitGamma.Main.DirectionalSymmetry
public import ASDExplicitGamma.Main.DirectionalCovariance
public import ASDExplicitGamma.Variational.LocalizedBlockSpace

/-! Actual-law averaging of the samplewise directional covariance matrices. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Triadic
open Algsuperdiff.Frozen.Assumptions
open ASDExplicitGamma.Scalar
open ASDExplicitGamma.Response ASDExplicitGamma.Native
open ASDExplicitGamma.Variational
open Algsuperdiff.Section3.Cutoff
open scoped ENNReal

/-- If an actual-sample matrix is symmetric and transforms by quarter-turn
conjugation, its expected matrix has equal diagonal entries and opposite
off-diagonal entries. The actual cutoff law supplies the rotation invariance. -/
theorem main_expected_matrix_half_trace_of_quarter_turn
    (M : ABKModel 2)
    (N : CutoffSample 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (Theta : CutoffSample 2 → ℝ) (xi : ℝ)
    (hInt : ∀ i j, Integrable (fun ω => N ω i j)
      (Cutoff.cutoffSampleLaw M).toMeasure)
    (hSym : ∀ ω i j, N ω i j = N ω j i)
    (hCov : ∀ ω,
      N (rotateCutoffSample quarterTurn
        main_quarterTurn_isSignedPermutation ω) =
        matTranspose quarterTurn * N ω * quarterTurn)
    (hThetaInt : Integrable Theta (Cutoff.cutoffSampleLaw M).toMeasure)
    (hTrace : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      Matrix.trace (N ω) ≤ Theta ω)
    (hTheta : (∫ ω, Theta ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ xi) :
    let A : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
      ∫ ω, N ω i j ∂(Cutoff.cutoffSampleLaw M).toMeasure
    A 0 1 = 0 ∧ A 1 0 = 0 ∧ A 0 0 ≤ xi / 2 ∧ A 1 1 ≤ xi / 2 := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let A : Matrix (Fin 2) (Fin 2) ℝ := fun i j => ∫ ω, N ω i j ∂μ
  have hRel := main_expected_matrix_quarter_turn_relations M N hInt hCov
  have hSymA : A 0 1 = A 1 0 := by
    dsimp [A]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun ω => hSym ω 0 1)
  have hTraceInt : Integrable (fun ω => Matrix.trace (N ω)) μ := by
    have hsum : Integrable
        ((fun ω => N ω 0 0) + (fun ω => N ω 1 1)) μ :=
      (hInt 0 0).add (hInt 1 1)
    apply hsum.congr
    filter_upwards with ω
    simp [Matrix.trace_fin_two, Pi.add_apply]
  have hTraceEq : Matrix.trace A =
      ∫ ω, Matrix.trace (N ω) ∂μ := by
    calc
      Matrix.trace A = A 0 0 + A 1 1 := by simp [Matrix.trace_fin_two]
      _ = (∫ ω, N ω 0 0 ∂μ) + ∫ ω, N ω 1 1 ∂μ := rfl
      _ = ∫ ω, N ω 0 0 + N ω 1 1 ∂μ :=
        (integral_add (hInt 0 0) (hInt 1 1)).symm
      _ = ∫ ω, Matrix.trace (N ω) ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun ω => by
          simp [Matrix.trace_fin_two])
  have hTraceMean : Matrix.trace A ≤ xi := by
    calc
      Matrix.trace A = ∫ ω, Matrix.trace (N ω) ∂μ := hTraceEq
      _ ≤ ∫ ω, Theta ω ∂μ := integral_mono_ae hTraceInt hThetaInt hTrace
      _ ≤ xi := hTheta
  have hIso := main_quarter_turn_covariance_half_bound A xi
    hSymA hRel.1 hRel.2.1 hTraceMean
  simpa [A] using hIso

end ASDExplicitGamma.Main

end
