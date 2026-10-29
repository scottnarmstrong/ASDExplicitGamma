/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Main.DirectionalSymmetry
public import ASDExplicitGamma.Scalar.SmoothFeedbackGammaRotation
public import ASDExplicitGamma.Scalar.SmoothFeedbackResponse
public import ASDExplicitGamma.Scalar.SmoothFeedbackCellTransport
public import ASDExplicitGamma.Scalar.SmoothFeedbackGammaMatrix

/-! Matrix covariance and the annealed planar half-trace identity for the
actual directional affine Gram. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization
open Algsuperdiff.Section3

noncomputable section

private theorem gamma_matrix_eq_of_quadratic_eq_and_symm
    {A B : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : ∀ i j, A i j = A j i) (hB : ∀ i j, B i j = B j i)
    (hquad : ∀ e : Vec 2,
      vecDot e (matVecMul A e) = vecDot e (matVecMul B e)) :
    A = B := by
  have h0 := hquad (basisVec 0)
  have h1 := hquad (basisVec 1)
  have hsum := hquad (basisVec 0 + basisVec 1)
  have h00 : A 0 0 = B 0 0 := by
    simpa [vecDot, matVecMul, Fin.sum_univ_two, basisVec] using h0
  have h11 : A 1 1 = B 1 1 := by
    simpa [vecDot, matVecMul, Fin.sum_univ_two, basisVec] using h1
  have hcross : A 0 1 = B 0 1 := by
    have hsum' : A 0 0 + A 0 1 + (A 1 0 + A 1 1) =
        B 0 0 + B 0 1 + (B 1 0 + B 1 1) := by
      simpa [vecDot, matVecMul, Fin.sum_univ_two, basisVec] using hsum
    rw [hA 1 0, hB 1 0] at hsum'
    linarith
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact hcross
  · calc
      A 1 0 = A 0 1 := hA 1 0
      _ = B 0 1 := hcross
      _ = B 1 0 := hB 0 1
  · exact h11

/-- The actual affine polarization matrix is symmetric sample by sample. -/
theorem smooth_feedback_gamma_matrix_symmetric
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) (i j : Fin 2) :
    smoothFeedbackCellGammaMatrix M m Q ω i j =
      smoothFeedbackCellGammaMatrix M m Q ω j i := by
  unfold smoothFeedbackCellGammaMatrix
  rw [add_comm (basisVec i) (basisVec j)]
  ring

private theorem matVecMul_mul' (A B : Mat 2) (x : Vec 2) :
    matVecMul (A * B) x = matVecMul A (matVecMul B x) := by
  ext i
  simp [matVecMul, Matrix.mul_apply, Fin.sum_univ_two]
  ring

private theorem vecDot_transpose_mulVec (R : Mat 2) (x y : Vec 2) :
    vecDot x (matVecMul (matTranspose R) y) =
      vecDot (matVecMul R x) y := by
  simp [vecDot, matVecMul, matTranspose, Matrix.transpose_apply,
    Fin.sum_univ_two]
  ring

/-- The actual cell Gamma matrix is covariant under the genuine cutoff-sample
quarter-turn about an arbitrary triadic cell center. -/
theorem smooth_feedback_gamma_matrix_centeredQuarterTurn
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (ω : Cutoff.CutoffSample 2) :
    smoothFeedbackCellGammaMatrix M m Q
        (centeredQuarterTurnCutoffSample Q ω) =
      matTranspose quarterTurn *
        smoothFeedbackCellGammaMatrix M m Q ω * quarterTurn := by
  let R : Mat 2 := quarterTurn
  have hMatrix :
      smoothFeedbackCellGammaMatrix M m Q
        (centeredQuarterTurnCutoffSample Q ω) =
        matTranspose R * smoothFeedbackCellGammaMatrix M m Q ω * R := by
    refine gamma_matrix_eq_of_quadratic_eq_and_symm
      (A := smoothFeedbackCellGammaMatrix M m Q
        (centeredQuarterTurnCutoffSample Q ω))
      (B := matTranspose R * smoothFeedbackCellGammaMatrix M m Q ω * R)
      ?_ ?_ ?_
    · intro i j
      exact smooth_feedback_gamma_matrix_symmetric M m Q
        (centeredQuarterTurnCutoffSample Q ω) i j
    · intro i j
      have hN : ∀ i j,
          smoothFeedbackCellGammaMatrix M m Q ω i j =
            smoothFeedbackCellGammaMatrix M m Q ω j i := by
        intro i j
        exact smooth_feedback_gamma_matrix_symmetric M m Q ω i j
      have hNtranspose :
          (smoothFeedbackCellGammaMatrix M m Q ω).transpose =
            smoothFeedbackCellGammaMatrix M m Q ω := by
        ext i j
        exact hN j i
      have hBtranspose :
          (matTranspose R * smoothFeedbackCellGammaMatrix M m Q ω * R).transpose =
            matTranspose R * smoothFeedbackCellGammaMatrix M m Q ω * R := by
        rw [Matrix.transpose_mul, Matrix.transpose_mul, hNtranspose]
        simp [matTranspose, Matrix.mul_assoc]
      have h := congrArg
        (fun A : Matrix (Fin 2) (Fin 2) ℝ => A i j) hBtranspose
      simpa [Matrix.transpose_apply] using h.symm
    · intro e
      have hGamma := smooth_feedback_cell_directional_gamma_centeredQuarterTurn
        M m Q ω e
      have hLeft := smooth_feedback_cell_gamma_matrix_quadratic_form
        M m Q (centeredQuarterTurnCutoffSample Q ω) e
      have hRight := smooth_feedback_cell_gamma_matrix_quadratic_form
        M m Q ω (matVecMul R e)
      let N := smoothFeedbackCellGammaMatrix M m Q ω
      have hTransform :
          vecDot (matVecMul R e) (matVecMul N (matVecMul R e)) =
            vecDot e (matVecMul (matTranspose R * N * R) e) := by
        rw [matVecMul_mul', matVecMul_mul']
        have htrans := vecDot_transpose_mulVec R e
          (matVecMul N (matVecMul R e))
        calc
          _ = vecDot (matVecMul R e) (matVecMul N (matVecMul R e)) := rfl
          _ = _ := htrans.symm
      calc
        vecDot e (matVecMul
            (smoothFeedbackCellGammaMatrix M m Q
              (centeredQuarterTurnCutoffSample Q ω)) e) =
            smoothFeedbackCellDirectionalGamma M m Q e
              (centeredQuarterTurnCutoffSample Q ω) := hLeft
        _ = smoothFeedbackCellDirectionalGamma M m Q
              (matVecMul R e) ω := by simpa [R] using hGamma
        _ = vecDot (matVecMul R e) (matVecMul N (matVecMul R e)) := hRight.symm
        _ = vecDot e (matVecMul (matTranspose R * N * R) e) := hTransform
  simpa [R] using hMatrix

private theorem expected_matrix_centeredQuarterTurn_relations
    (M : ABKModel 2) (Q : TriadicCube 2)
    (N : Cutoff.CutoffSample 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hInt : ∀ i j, Integrable (fun ω => N ω i j)
      (Cutoff.cutoffSampleLaw M).toMeasure)
    (hCov : ∀ ω,
      N (centeredQuarterTurnCutoffSample Q ω) =
        matTranspose quarterTurn * N ω * quarterTurn) :
    let A : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
      ∫ ω, N ω i j ∂(Cutoff.cutoffSampleLaw M).toMeasure
    A 0 0 = A 1 1 ∧ A 0 1 = -A 1 0 ∧ A 1 0 = -A 0 1 := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let ρ : Cutoff.CutoffSample 2 → Cutoff.CutoffSample 2 :=
    centeredQuarterTurnCutoffSample Q
  let A : Matrix (Fin 2) (Fin 2) ℝ := fun i j => ∫ ω, N ω i j ∂μ
  have hρMeas : Measurable ρ := by
    let z := triadicCubeShift Q
    change Measurable (Cutoff.translateCutoffSample (-z) ∘
      Cutoff.rotateCutoffSample quarterTurn
        Main.main_quarterTurn_isSignedPermutation ∘
      Cutoff.translateCutoffSample z)
    exact (Cutoff.measurable_translateCutoffSample (-z)).comp
      ((Cutoff.measurable_rotateCutoffSample quarterTurn
        Main.main_quarterTurn_isSignedPermutation).comp
        (Cutoff.measurable_translateCutoffSample z))
  have hρMap : Measure.map ρ μ = μ := by
    simpa [ρ, μ] using
      map_centeredQuarterTurnCutoffSample_cutoffSampleLaw M Q
  have hIntegralComp (i j : Fin 2) :
      (∫ ω, N ω i j ∂μ) = ∫ ω, N (ρ ω) i j ∂μ := by
    have hNMap : AEStronglyMeasurable (fun ω => N ω i j)
        (Measure.map ρ μ) := by
      simpa [hρMap] using (hInt i j).aestronglyMeasurable
    calc
      (∫ ω, N ω i j ∂μ) = ∫ ω, N ω i j ∂(Measure.map ρ μ) := by
        rw [hρMap]
      _ = ∫ ω, N (ρ ω) i j ∂μ :=
        integral_map hρMeas.aemeasurable hNMap
  have hCov00 (ω : Cutoff.CutoffSample 2) : N (ρ ω) 0 0 = N ω 1 1 := by
    have h := congrArg (fun B : Matrix (Fin 2) (Fin 2) ℝ => B 0 0) (hCov ω)
    simpa [ρ, quarterTurn, matTranspose, Matrix.mul_apply,
      Fin.sum_univ_two] using h
  have hCov01 (ω : Cutoff.CutoffSample 2) : N (ρ ω) 0 1 = -N ω 1 0 := by
    have h := congrArg (fun B : Matrix (Fin 2) (Fin 2) ℝ => B 0 1) (hCov ω)
    simpa [ρ, quarterTurn, matTranspose, Matrix.mul_apply,
      Fin.sum_univ_two] using h
  have hCov10 (ω : Cutoff.CutoffSample 2) : N (ρ ω) 1 0 = -N ω 0 1 := by
    have h := congrArg (fun B : Matrix (Fin 2) (Fin 2) ℝ => B 1 0) (hCov ω)
    simpa [ρ, quarterTurn, matTranspose, Matrix.mul_apply,
      Fin.sum_univ_two] using h
  refine ⟨?_, ?_, ?_⟩
  · calc
      A 0 0 = ∫ ω, N (ρ ω) 0 0 ∂μ := hIntegralComp 0 0
      _ = ∫ ω, N ω 1 1 ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hCov00
      _ = A 1 1 := rfl
  · calc
      A 0 1 = ∫ ω, N (ρ ω) 0 1 ∂μ := hIntegralComp 0 1
      _ = ∫ ω, -N ω 1 0 ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hCov01
      _ = -A 1 0 := by rw [integral_neg]
  · calc
      A 1 0 = ∫ ω, N (ρ ω) 1 0 ∂μ := hIntegralComp 1 0
      _ = ∫ ω, -N ω 0 1 ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hCov10
      _ = -A 0 1 := by rw [integral_neg]

/-- The actual OLD-law directional half-trace identity holds on any triadic
cell. The cell-centered sample action preserves the whole cutoff law, while
the source-response covariance comes from the arbitrary-cell centered
quarter-turn theorem above. -/
theorem smooth_feedback_expected_directional_gamma_half_trace_cell
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (e : Vec 2)
    (hInt : ∀ i j : Fin 2,
      Integrable
        (fun ω : Cutoff.CutoffSample 2 =>
          smoothFeedbackCellGammaMatrix M m Q ω i j)
        (Cutoff.cutoffSampleLaw M).toMeasure) :
    (∫ ω, smoothFeedbackCellDirectionalGamma M m Q e ω
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) =
      (((∫ ω, smoothFeedbackCellGammaMatrix M m Q ω 0 0
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) +
        ∫ ω, smoothFeedbackCellGammaMatrix M m Q ω 1 1
          ∂(Cutoff.cutoffSampleLaw M).toMeasure) / 2) * vecNormSq e := by
  classical
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let N : Cutoff.CutoffSample 2 → Matrix (Fin 2) (Fin 2) ℝ :=
    fun ω => smoothFeedbackCellGammaMatrix M m Q ω
  let A : Matrix (Fin 2) (Fin 2) ℝ := fun i j => ∫ ω, N ω i j ∂μ
  have hNInt : ∀ i j, Integrable (fun ω => N ω i j) μ := by
    intro i j
    simpa [N, μ] using hInt i j
  have hCov : ∀ ω,
      N (centeredQuarterTurnCutoffSample Q ω) =
        matTranspose quarterTurn * N ω * quarterTurn := by
    intro ω
    simpa [N] using
      smooth_feedback_gamma_matrix_centeredQuarterTurn M m Q ω
  have hRelations := expected_matrix_centeredQuarterTurn_relations
    M Q N hNInt hCov
  have hA_symm : ∀ i j, A i j = A j i := by
    intro i j
    have hentry (ω : Cutoff.CutoffSample 2) : N ω i j = N ω j i := by
      exact smooth_feedback_gamma_matrix_symmetric M m Q ω i j
    dsimp [A]
    exact integral_congr_ae (Filter.Eventually.of_forall hentry)
  have hA00 : A 0 0 = A 1 1 := by simpa [A] using hRelations.1
  have hA01 : A 0 1 = 0 := by
    have hrel : A 0 1 = -A 1 0 := by simpa [A] using hRelations.2.1
    have h10zero : A 1 0 = 0 := by
      rw [hA_symm 0 1] at hrel
      linarith
    calc
      A 0 1 = A 1 0 := hA_symm 0 1
      _ = 0 := h10zero
  have hA10 : A 1 0 = 0 := by
    calc
      A 1 0 = A 0 1 := (hA_symm 0 1).symm
      _ = 0 := hA01
  have hAtranspose : A.transpose = A := by
    ext i j
    exact hA_symm j i
  have hArot : quarterTurn.transpose * A * quarterTurn = A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [quarterTurn, Matrix.mul_apply, Matrix.transpose_apply,
        Fin.sum_univ_two, hA00, hA01, hA10]
  have hIntegralQuadratic :
      (∫ ω, smoothFeedbackCellDirectionalGamma M m Q e ω ∂μ) =
        ∑ i : Fin 2, ∑ j : Fin 2, e i * e j * A i j := by
    have hpoint (ω : Cutoff.CutoffSample 2) :
        smoothFeedbackCellDirectionalGamma M m Q e ω =
          ∑ i : Fin 2, ∑ j : Fin 2, e i * e j * N ω i j := by
      rw [← smooth_feedback_cell_gamma_matrix_quadratic_form]
      simp [vecDot, matVecMul, Fin.sum_univ_two, N]
      ring
    have hscaled (i j : Fin 2) :
        Integrable (fun ω => (e i * e j) * N ω i j) μ :=
      (hNInt i j).const_mul (e i * e j)
    have hinner (i : Fin 2) :
        Integrable (fun ω => ∑ j : Fin 2, e i * e j * N ω i j) μ := by
      have hadd (ω : Cutoff.CutoffSample 2) :
          (∑ j : Fin 2, e i * e j * N ω i j) =
            (e i * e 0) * N ω i 0 + (e i * e 1) * N ω i 1 := by
        simp [Fin.sum_univ_two, mul_assoc]
      have hfun : (fun ω => ∑ j : Fin 2, e i * e j * N ω i j) =
          (fun ω => (e i * e 0) * N ω i 0 + (e i * e 1) * N ω i 1) := by
        funext ω
        exact hadd ω
      rw [hfun]
      exact (hscaled i 0).add (hscaled i 1)
    calc
      _ = ∫ ω, ∑ i : Fin 2, ∑ j : Fin 2, e i * e j * N ω i j ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall hpoint)
      _ = ∑ i : Fin 2, ∫ ω, ∑ j : Fin 2, e i * e j * N ω i j ∂μ := by
        rw [integral_finsetSum _ (fun i _ => hinner i)]
      _ = ∑ i : Fin 2, ∑ j : Fin 2, ∫ ω, (e i * e j) * N ω i j ∂μ := by
        congr 1
        ext i
        rw [integral_finsetSum _ (fun j _ => hscaled i j)]
      _ = ∑ i : Fin 2, ∑ j : Fin 2, e i * e j * A i j := by
        simp [A, μ, integral_const_mul]
  have hIso := quarter_turn_symmetric_form_isotropic A hAtranspose hArot e
  have hIso' :
      (∑ i : Fin 2, ∑ j : Fin 2, e i * e j * A i j) =
        ((A 0 0 + A 1 1) / 2) * vecNormSq e := by
    have hExpand :
        (∑ i : Fin 2, ∑ j : Fin 2, e i * e j * A i j) =
          ∑ i : Fin 2, e i * (A.mulVec e) i := by
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
    calc
      _ = ∑ i : Fin 2, e i * (A.mulVec e) i := hExpand
      _ = ((A 0 0 + A 1 1) / 2) * (e 0 ^ 2 + e 1 ^ 2) := hIso
      _ = ((A 0 0 + A 1 1) / 2) * vecNormSq e := by
        congr 1
        simp [vecNormSq, vecDot, Fin.sum_univ_two]
        ring
  calc
    _ = ∑ i : Fin 2, ∑ j : Fin 2, e i * e j * A i j := hIntegralQuadratic
    _ = _ := by simpa [A, μ] using hIso'

end
end ASDExplicitGamma.Scalar
