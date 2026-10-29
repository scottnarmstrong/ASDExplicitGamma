module

public import ASDExplicitGamma.Main.EOscillationInverseHistoryAdapter
public import ASDExplicitGamma.Main.AffineMatrixMoments
public import ASDExplicitGamma.Main.DirectionalPhysicalFlux
public import ASDExplicitGamma.Scalar.InverseHistoryBlocks

import Mathlib.Tactic

/-! The global inverse bank controls the `sigmaBar`-weighted physical inverse
trace in the stationary OLD frame. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian
  ASDExplicitGamma.Inverse ASDExplicitGamma.Model ASDExplicitGamma.Native
  ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational
open Algsuperdiff.Section3
open scoped ENNReal

noncomputable section

/-- The OLD-frame inverse trace is the trace of the actual source-cell
coefficient in the response frame. -/
private theorem main_affine_inverse_trace_frame_eq
    (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (ω : Cutoff.CutoffSample 2) :
    mainInsertionInverseTrace M m (m - 5) t ω =
      Matrix.trace ((coarseBlockMatrix (cubeSet (originCube 2 (m - 5)))
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
          (mainInsertionSkewCoefficient m t (originCube 2 (m - 5)) ω))).lowerRight) := by
  let Q : TriadicCube 2 := originCube 2 (m - 5)
  let σ : ℝ := Annealed.sigmaBar M m
  let a : CoeffField 2 := responseFramePlanarCoefficientField M.nu σ
    (mainInsertionSkewCoefficient m t Q ω)
  let c : CoeffField 2 := (Model.partialInsertedCoefficient M m t ω).toFun
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M m).1
  obtain ⟨ell, hK⟩ := Gaussian.exists_originCube_containing_compact
    (closure (cubeSet Q)) (isBounded_cubeSet Q).isCompact_closure
  have hEll : IsEllipticFieldOn M.nu _ (cubeSet Q) c :=
    Model.partialInsertedCoefficient_isEllipticFieldOn M ell m ω
      ⟨ht.1, ht.2⟩ (measurableSet_cubeSet Q)
      (fun x hx => hK (subset_closure hx))
  have hCoeff : a =ᵐ[volumeMeasureOn (openCubeSet Q)] (σ⁻¹ • c) := by
    filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x hx
    exact main_directional_response_frame_eq_scaled_partial_coefficient
      M m t Q ω x hx
  have hMatrixOpen : coarseBlockMatrix (openCubeSet Q) a =
      coarseBlockMatrix (openCubeSet Q) (σ⁻¹ • c) :=
    coarseBlockMatrix_congr_of_ae_eq hCoeff
  have hMatrix : coarseBlockMatrix (cubeSet Q) a =
      coarseBlockMatrix (cubeSet Q) (σ⁻¹ • c) := by
    rw [cube_coarseMatrix_eq_open Q a,
      cube_coarseMatrix_eq_open Q (σ⁻¹ • c)]
    exact hMatrixOpen
  have hScale := coarseBlockMatrix_smul_elliptic_triCube M.nu_pos hEll
    (inv_pos.mpr hσ)
  have hpow : (Real.sqrt σ⁻¹) ^ (-2 : ℤ) = σ := by
    rw [zpow_neg, zpow_ofNat,
      Real.sq_sqrt (inv_nonneg.mpr hσ.le), inv_inv]
  have hLower : (coarseBlockMatrix (cubeSet Q) a).lowerRight =
      σ • (coarseBlockMatrix (cubeSet Q) c).lowerRight := by
    calc
      _ = (coarseMatrixRescale (Real.sqrt σ⁻¹)
          (coarseBlockMatrix (cubeSet Q) c)).lowerRight := by
            rw [hMatrix, hScale]
      _ = _ := by
        ext i j
        change (Real.sqrt σ⁻¹) ^ (-2 : ℤ) *
            (coarseBlockMatrix (cubeSet Q) c).lowerRight i j =
          σ * (coarseBlockMatrix (cubeSet Q) c).lowerRight i j
        rw [hpow]
  have htrace : Matrix.trace (coarseBlockMatrix (cubeSet Q) a).lowerRight =
      σ * Matrix.trace (coarseBlockMatrix (cubeSet Q) c).lowerRight := by
    rw [hLower]
    exact Matrix.trace_smul σ _
  change σ * Matrix.trace (coarseBlockMatrix (cubeSet Q) c).lowerRight = _
  rw [← htrace]

/-- The global inverse-history bank gives the expected OLD-frame inverse
trace bound on the actual inserted q3 source square. -/
theorem main_affine_inverse_trace_frame_integral
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hgamma : M.gamma ≤ gammaZero) (N : ℤ)
    (hpast : ∀ k < N, nativeInductionState M h k)
    (m : ℤ) (hm : m < N) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (∫ ω, (Annealed.sigmaBar M m : ℝ) *
      Matrix.trace (coarseBlockMatrix (cubeSet (originCube 2 (m - 5)))
        (Model.partialInsertedCoefficient M m t ω).toFun).lowerRight
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ 2 * mainBeta := by
  let Q : TriadicCube 2 := originCube 2 (m - 5)
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let B : Cutoff.CutoffSample 2 → ℝ :=
    fun ω => (mainCutoffQ3SourceInverseBankMax M m t ω).toReal
  let d : Cutoff.CutoffSample 2 → ℝ := mainInsertionInverseTrace M m (m - 5) t
  have hpastM : ∀ k < m, nativeInductionState M h k := by
    intro k hk
    exact hpast k (lt_trans hk hm)
  have hBank := main_q3_source_inverse_bank_and_history
    M h hM hgamma m hpastM t ht
  have hBMem : MemLp B 2 μ := by
    simpa [B, μ] using hBank.2.1
  have hBNorm : lpNorm B 2 μ ≤ mainBeta := by
    simpa [B, μ] using hBank.2.2.1
  have hBnonneg : ∀ ω, 0 ≤ B ω := by
    intro ω
    exact ENNReal.toReal_nonneg
  have hBmean : (∫ ω, B ω ∂μ) ≤ mainBeta := by
    have hmono := eLpNorm_le_eLpNorm_of_exponent_le (f := B) (μ := μ)
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have hnorm := ENNReal.toReal_mono hBMem.eLpNorm_ne_top hmono
    change lpNorm B 1 μ ≤ lpNorm B 2 μ at hnorm
    rw [lpNorm_one_eq_integral_norm hBMem.aestronglyMeasurable] at hnorm
    simp only [Real.norm_eq_abs, abs_of_nonneg (hBnonneg _)] at hnorm
    exact hnorm.trans hBNorm
  have h2BInt : Integrable (fun ω => 2 * B ω) μ :=
    (hBMem.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).const_mul 2
  have hdInt : Integrable d μ := by
    have hEntry (i : Fin 2) : Integrable
        (fun ω => blockMatEntry
          (coarseBlockMatrix (cubeSet Q)
            (Model.partialInsertedCoefficient M m t ω).toFun)
          (Sum.inr i) (Sum.inr i)) μ := by
      simpa [μ, Q] using mainInsertion_coarseBlockMatrix_entry_integrable
        M m (m - 5) t ⟨ht.1, ht.2⟩ (Sum.inr i) (Sum.inr i)
    have hsum : Integrable (fun ω =>
        ∑ i : Fin 2, (Annealed.sigmaBar M m : ℝ) * blockMatEntry
          (coarseBlockMatrix (cubeSet Q)
            (Model.partialInsertedCoefficient M m t ω).toFun)
          (Sum.inr i) (Sum.inr i)) μ := by
      exact integrable_finsetSum Finset.univ
        (fun i _ => (hEntry i).const_mul (Annealed.sigmaBar M m : ℝ))
    have hEq : (fun ω => ∑ i : Fin 2,
        (Annealed.sigmaBar M m : ℝ) * blockMatEntry
          (coarseBlockMatrix (cubeSet Q)
            (Model.partialInsertedCoefficient M m t ω).toFun)
          (Sum.inr i) (Sum.inr i)) = d := by
      funext ω
      simp [d, mainInsertionInverseTrace, Q, Matrix.trace, blockMatEntry]
      ring
    rw [← hEq]
    exact hsum
  have hdepth : ∀ᵐ ω ∂μ,
      lemmaVInverseDepthMax Q
          (responseFramePlanarCoefficientField M.nu
            (Annealed.sigmaBar M m : ℝ)
            (mainInsertionSkewCoefficient m t Q ω)) 0 ≤ B ω := by
    filter_upwards [hBank.2.2.2] with ω hhistory
    exact (bank_inverse_depth_zero_le_history Q
      (responseFramePlanarCoefficientField M.nu
        (Annealed.sigmaBar M m : ℝ)
        (mainInsertionSkewCoefficient m t Q ω))
      (responseFramePlanarCoefficientField_isElliptic
        (measurableSet_openCubeSet Q) M.nu (Annealed.sigmaBar M m : ℝ)
        M.nu_pos (Annealed.sigmaBar_characterization M m).1
        (mainInsertionSkewCoefficient m t Q ω))
      (Real.one_lt_rpow (by norm_num) (by norm_num))).trans hhistory
  have hdBound : ∀ᵐ ω ∂μ, d ω ≤ 2 * B ω := by
    filter_upwards [hdepth] with ω hω
    have hEllFrame : IsEllipticFieldOn (M.nu / (Annealed.sigmaBar M m : ℝ)) _
        (openCubeSet Q)
        (responseFramePlanarCoefficientField M.nu
          (Annealed.sigmaBar M m : ℝ)
          (mainInsertionSkewCoefficient m t Q ω)) :=
      responseFramePlanarCoefficientField_isElliptic
        (measurableSet_openCubeSet Q) M.nu (Annealed.sigmaBar M m : ℝ)
        M.nu_pos (Annealed.sigmaBar_characterization M m).1
        (mainInsertionSkewCoefficient m t Q ω)
    have hdepth0 : lemmaVInverseDepthMax Q
        (responseFramePlanarCoefficientField M.nu
          (Annealed.sigmaBar M m : ℝ)
          (mainInsertionSkewCoefficient m t Q ω)) 0 =
        Book.Ch02.matrixNorm
          (coarseBlockMatrix (cubeSet Q)
            (responseFramePlanarCoefficientField M.nu
              (Annealed.sigmaBar M m : ℝ)
              (mainInsertionSkewCoefficient m t Q ω))).lowerRight := by
      unfold lemmaVInverseDepthMax
      simp only [descendantsAtDepth_zero, Book.Ch02.finsetSupReal,
        Finset.coe_singleton, Set.image_singleton, csSup_singleton]
      exact congrArg Book.Ch02.matrixNorm
        (inverse_history_lowerRight Q _ hEllFrame)
    let C := (coarseBlockMatrix (cubeSet Q)
      (responseFramePlanarCoefficientField M.nu
        (Annealed.sigmaBar M m : ℝ)
        (mainInsertionSkewCoefficient m t Q ω))).lowerRight
    have h0 := (le_abs_self (C 0 0)).trans
      (clipped_matrix_entry_abs_le_norm C 0 0)
    have h1 := (le_abs_self (C 1 1)).trans
      (clipped_matrix_entry_abs_le_norm C 1 1)
    have h0' : C 0 0 ≤ Book.Ch02.matrixNorm C := by
      simpa only [Book.Ch02.matrixNorm_eq_matrixOperatorNorm,
        Book.Ch02.matrixOperatorNorm] using h0
    have h1' : C 1 1 ≤ Book.Ch02.matrixNorm C := by
      simpa only [Book.Ch02.matrixNorm_eq_matrixOperatorNorm,
        Book.Ch02.matrixOperatorNorm] using h1
    have htrace : Matrix.trace C ≤ 2 * Book.Ch02.matrixNorm C := by
      simp only [Matrix.trace, Fin.sum_univ_two, Matrix.diag_apply]
      nlinarith only [h0', h1']
    have hEq := main_affine_inverse_trace_frame_eq M m t ht ω
    calc
      d ω = Matrix.trace C := by
        change mainInsertionInverseTrace M m (m - 5) t ω = _
        rw [hEq]
      _ ≤ 2 * lemmaVInverseDepthMax Q
          (responseFramePlanarCoefficientField M.nu
            (Annealed.sigmaBar M m : ℝ)
            (mainInsertionSkewCoefficient m t Q ω)) 0 := by
        rw [hdepth0]
        exact htrace
      _ ≤ 2 * B ω := mul_le_mul_of_nonneg_left hω (by norm_num)
  have hmean2 : (∫ ω, 2 * B ω ∂μ) ≤ 2 * mainBeta := by
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hBmean (by norm_num)
  calc
    (∫ ω, d ω ∂μ) ≤ ∫ ω, 2 * B ω ∂μ := integral_mono_ae hdInt h2BInt hdBound
    _ ≤ 2 * mainBeta := hmean2

end
end ASDExplicitGamma.Main
