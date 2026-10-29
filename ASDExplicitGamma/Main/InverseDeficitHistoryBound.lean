module

public import ASDExplicitGamma.Main.InverseLowerCenteredGlobalBank
public import ASDExplicitGamma.Main.InverseObservable
public import ASDExplicitGamma.Main.InverseDeficitBank
public import ASDExplicitGamma.Inverse.ClippedMatrixEntryCap
public import ASDExplicitGamma.Inverse.PureFluxGeneratorBankLaw
public import ASDExplicitGamma.Inverse.RawShellBandGenerator

/-! The actual q3 inverse observable is controlled by the source bank's
complete local history on its finite event. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Response
  ASDExplicitGamma.Triadic ASDExplicitGamma.Variational ASDExplicitGamma.Inverse
open Algsuperdiff.Section3

/-- On the global bank's finite-history event, the actual source inverse trace
is nonnegative and bounded by twice the same max-based history used by the
q3 source-root row. -/
theorem main_actual_inverse_observable_source_history_bounds_of_native_state
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (s : ℕ) (hs : 1 ≤ s ∧ s ≤ 40)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hpast : ∀ j < n, nativeInductionState M h j) :
    let Q := originCube 2 n
    let σ := (Annealed.sigmaBar M n : ℝ)
    let x := modelInsertedScalar (closure (cubeSet Q)) (n + (s : ℤ) - 1) t
    let B (ω : Cutoff.CutoffSample 2) :=
      (bankFiniteRootHistoryMax (bankLocalRoots Q 5) M n (n + 40)
        (bankPartialInsertionWeights n s t) ω).toReal
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      0 ≤ mainInverseObservable n M.nu σ (x ω) ∧
        mainInverseObservable n M.nu σ (x ω) ≤ 2 * B ω := by
  intro Q σ x B
  have hBank := main_local_history_global_bank_of_native_state
    M h hM hg n s t ht hpast
  filter_upwards [hBank.history_finite] with ω hfinite
  let xω := x ω
  let k := pureFluxOpenResponseRestriction n xω
  let kClosed : ResponseCoefficient (cubeSet Q) :=
    ContinuousMap.linearIsometryBoundedOfCompact (closure (cubeSet Q)) ℝ ℝ xω
  let P := coarseBlockMatrix (cubeSet Q)
    (responsePlanarCoefficientField M.nu kClosed)
  let af := responseFramePlanarCoefficientField M.nu σ k
  let A := coarseBlockMatrix (cubeSet Q) af
  let D := bankInverseTraceObservable n M.nu σ M.nu_pos
    (Annealed.sigmaBar_characterization M n).1 xω
  have hEll : IsEllipticFieldOn (M.nu / σ)
      (((M.nu / σ) ^ 2 + (‖k‖ / σ) ^ 2) / (M.nu / σ))
      (openCubeSet Q) af :=
    responseFramePlanarCoefficientField_isElliptic
      (measurableSet_openCubeSet Q) M.nu σ M.nu_pos
      (Annealed.sigmaBar_characterization M n).1 k
  have hdepthZero : lemmaVInverseDepthMax Q af 0 =
      Book.Ch02.matrixNorm A.lowerRight := by
    unfold lemmaVInverseDepthMax
    simp only [descendantsAtDepth_zero, Book.Ch02.finsetSupReal,
      Finset.coe_singleton, Set.image_singleton, csSup_singleton]
    exact congrArg Book.Ch02.matrixNorm
      (Scalar.inverse_history_lowerRight Q af hEll)
  have hframe : A = frameMatrix σ
      P := by
    have hae : af =ᵐ[volume.restrict (openCubeSet Q)]
        responseFramePlanarCoefficientField M.nu σ kClosed := by
      filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with y hy
      change responseFramePlanarCoefficientField M.nu σ k y = _
      rw [responseFramePlanarCoefficientField_apply,
        responseFramePlanarCoefficientField_apply,
        pureFluxOpenResponseRestriction_value n xω hy]
      rw [responseCoefficientExtension_eq kClosed
        (openCubeSet_subset_cubeSet Q hy),
        ContinuousMap.linearIsometryBoundedOfCompact_apply_apply]
    calc
      A = coarseBlockMatrix (cubeSet Q)
          (responseFramePlanarCoefficientField M.nu σ kClosed) := by
        change coarseBlockMatrix (cubeSet Q) af = _
        rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube Q,
          coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube Q]
        exact coarseBlockMatrix_congr_of_ae_eq hae
      _ = frameMatrix σ P :=
        response_coarseMatrix_frame_eq (Q := Q) (measurableSet_cubeSet Q)
          M.nu σ M.nu_pos (Annealed.sigmaBar_characterization M n).1 kClosed
  have hDframe : D = Matrix.trace A.lowerRight := by
    have h := raw_shell_band_bank_inverse_trace_eq_frame_trace M n xω
    dsimp [D, A, P, Q, σ, k, kClosed, xω] at h ⊢
    rw [h]
    rw [← hframe]
  have htraceNorm : Matrix.trace A.lowerRight ≤
      2 * Book.Ch02.matrixNorm A.lowerRight := by
    let C := A.lowerRight
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
    simp only [Matrix.trace, Fin.sum_univ_two]
    dsimp [C]
    nlinarith only [h0', h1']
  have hdepth := bank_inverse_depth_zero_le_history Q af
    hEll (show 1 < (3 : ℝ) ^ (1 / 4 : ℝ) from
      Real.one_lt_rpow (by norm_num) (by norm_num))
  have hroot : Q ∈ descendantsAtDepth Q 0 := by simp
  have hmesh := pureFlux_bank_source_mesh_history_le M n s hs t ht ω
    0 (by norm_num) hfinite.ne hroot
  have hB : 0 ≤ B ω := ENNReal.toReal_nonneg
  have hphysicalEll := responsePlanarCoefficientField_isElliptic
    (measurableSet_cubeSet Q) M.nu M.nu_pos kClosed
  have hphysicalPos := coarseBlockMatrix_posDef M.nu_pos hphysicalEll
  have hdiag0 : 0 <
      P.lowerRight 0 0 := by
    simpa only [toFullBlockMat] using hphysicalPos.diag_pos (i := Sum.inr (0 : Fin 2))
  have hdiag1 : 0 <
      P.lowerRight 1 1 := by
    simpa only [toFullBlockMat] using hphysicalPos.diag_pos (i := Sum.inr (1 : Fin 2))
  have hnonneg : 0 ≤ mainInverseObservable n M.nu σ xω := by
    unfold mainInverseObservable
    change 0 ≤ σ * Matrix.trace P.lowerRight
    simp only [Matrix.trace, Fin.sum_univ_two, Matrix.diag_apply]
    exact mul_nonneg (Annealed.sigmaBar_characterization M n).1.le
      (add_nonneg hdiag0.le hdiag1.le)
  have hmain : mainInverseObservable n M.nu σ xω = D := by
    calc
      mainInverseObservable n M.nu σ xω = Matrix.trace A.lowerRight := by
        unfold mainInverseObservable
        rw [hframe]
        simp [frameMatrix, Matrix.trace, Matrix.diag_apply,
          Matrix.smul_apply, smul_eq_mul, P]
        ring
      _ = D := hDframe.symm
  have hupper : D ≤ 2 * B ω := by
    change D ≤ 2 *
      (bankFiniteRootHistoryMax (bankLocalRoots Q 5) M n (n + 40)
        (bankPartialInsertionWeights n s t) ω).toReal
    calc
      D = Matrix.trace A.lowerRight := hDframe
      _ ≤ 2 * Book.Ch02.matrixNorm A.lowerRight := htraceNorm
      _ = 2 * lemmaVInverseDepthMax Q af 0 := by rw [hdepthZero]
      _ ≤ 2 * lemmaVInverseHistory Q af ((3 : ℝ) ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hdepth (by norm_num)
      _ ≤ 2 * (bankFiniteRootHistoryMax (bankLocalRoots Q 5) M n (n + 40)
          (bankPartialInsertionWeights n s t) ω).toReal :=
        mul_le_mul_of_nonneg_left hmesh (by norm_num)
  exact ⟨hnonneg, by rw [hmain]; exact hupper⟩

private theorem main_actual_inverse_observable_measurable
    (M : ABKModel 2) (n : ℤ) (s : ℕ) (t : ℝ) :
    Measurable (fun ω : Cutoff.CutoffSample 2 =>
      mainInverseObservable n M.nu (Annealed.sigmaBar M n : ℝ)
        (modelInsertedScalar (closure (cubeSet (originCube 2 n)))
          (n + (s : ℤ) - 1) t ω)) := by
  let K := closure (cubeSet (originCube 2 n))
  obtain ⟨ell, hK⟩ := Gaussian.exists_originCube_containing_compact K
    (isBounded_cubeSet (originCube 2 n)).isCompact_closure
  have hscalar : Measurable (modelInsertedScalar K (n + (s : ℤ) - 1) t) := by
    change Measurable (fun ω => olderField K (n + (s : ℤ) - 1) ω +
      Real.sqrt t • shellFieldScalarRestriction K (ω.1 ((n + (s : ℤ) - 1) + 1)))
    exact (measurable_olderField K ell (n + (s : ℤ) - 1) hK).add
      (((measurable_shellFieldScalarRestriction K).comp
        ((measurable_pi_apply ((n + (s : ℤ) - 1) + 1)).comp
          measurable_subtype_coe)).const_smul (Real.sqrt t))
  have hσ : 0 < (Annealed.sigmaBar M n : ℝ) :=
    (Annealed.sigmaBar_characterization M n).1
  exact (mainInverseObservable_hasPolynomiallyBoundedC2Derivatives n M.nu
    (Annealed.sigmaBar M n : ℝ) M.nu_pos hσ).1.continuous.measurable.comp hscalar

/-- The actual global inverse bank controls the integrated cubic source term
for each q3 insertion shell. This is the bank-backed moment input consumed by
the inverse-deficit ODE. -/
theorem main_actual_inverse_deficit_cubic_integral_bound_of_native_state
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (s : ℕ) (hs : 1 ≤ s ∧ s ≤ 40)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hpast : ∀ j < n, nativeInductionState M h j) :
    let Q := originCube 2 n
    let σ := (Annealed.sigmaBar M n : ℝ)
    let x := modelInsertedScalar (closure (cubeSet Q)) (n + (s : ℤ) - 1) t
    ∫ ω,
        (bankFiniteRootHistoryMax (bankLocalRoots Q 5) M n (n + 40)
          (bankPartialInsertionWeights n s t) ω).toReal ^ 2 *
          mainInverseObservable n M.nu σ (x ω)
          ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      (inverseBankCap .globalInverse : ℝ) ^ 2 *
          (∫ ω, mainInverseObservable n M.nu σ (x ω)
            ∂(Cutoff.cutoffSampleLaw M).toMeasure) +
        2 * (2 * (inverseBankCap .globalInverse : ℝ) ^ 2 *
              (inverseBankReserve .globalInverse : ℝ) +
            3 * (inverseBankCap .globalInverse : ℝ) *
              (inverseBankReserve .globalInverse : ℝ) ^ 2 +
            (inverseBankReserve .globalInverse : ℝ) ^ 3) := by
  intro Q σ x
  let d : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    mainInverseObservable n M.nu σ (x ω)
  have hBank := main_local_history_global_bank_of_native_state
    M h hM hg n s t ht hpast
  have hdMeas : Measurable d := by
    simpa only [d, Q, σ, x] using main_actual_inverse_observable_measurable M n s t
  have hd := main_actual_inverse_observable_source_history_bounds_of_native_state
    M h hM hg n s hs t ht hpast
  have hd' : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      0 ≤ d ω ∧ d ω ≤ 2 *
        (bankFiniteRootHistoryMax (bankLocalRoots Q 5) M n (n + 40)
          (bankPartialInsertionWeights n s t) ω).toReal := by
    simpa [d, Q, σ, x] using hd
  simpa only [d, Q, σ, x] using
    main_inverse_deficit_cubic_integral_bound_of_global_bank M
      (bankLocalRoots Q 5) n (n + 40) (bankPartialInsertionWeights n s t) d
      hBank hdMeas hd'

/-- The padded source cubic and the observable itself are integrable under the
same actual global bank. This exposes the integrability needed to average a
pathwise trace-generator row. -/
theorem main_actual_inverse_deficit_padded_integrability_of_native_state
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (s : ℕ) (hs : 1 ≤ s ∧ s ≤ 40)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hpast : ∀ j < n, nativeInductionState M h j) :
    let Q := originCube 2 n
    let σ := (Annealed.sigmaBar M n : ℝ)
    let x := modelInsertedScalar (closure (cubeSet Q)) (n + (s : ℤ) - 1) t
    let B (ω : Cutoff.CutoffSample 2) :=
      (bankFiniteRootHistoryMax (bankLocalRoots Q 5) M n (n + 40)
        (bankPartialInsertionWeights n s t) ω).toReal
    let d (ω : Cutoff.CutoffSample 2) := mainInverseObservable n M.nu σ (x ω)
    Integrable d (Cutoff.cutoffSampleLaw M).toMeasure ∧
      Integrable (fun ω => (max 1 (B ω)) ^ 2 * d ω)
        (Cutoff.cutoffSampleLaw M).toMeasure := by
  intro Q σ x B d
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let Y : Cutoff.CutoffSample 2 → ENNReal :=
    bankFiniteRootHistoryMax (bankLocalRoots Q 5) M n (n + 40)
      (bankPartialInsertionWeights n s t)
  let Bstar : Cutoff.CutoffSample 2 → ℝ := fun ω => max 1 (B ω)
  have hBank := main_local_history_global_bank_of_native_state
    M h hM hg n s t ht hpast
  have hYmeas : Measurable Y := history_finite_max_measurable _ _
    (fun Q' => bank_root_inverse_history_measurable Q'.1 M n (n + 40)
      (bankPartialInsertionWeights n s t))
  have hBmeas : Measurable B := by
    exact ENNReal.measurable_toReal.comp hYmeas
  have hBstarMeas : Measurable Bstar := measurable_const.max hBmeas
  have hβ : 0 ≤ (inverseBankCap .globalInverse : ℝ) := by
    norm_num [inverseBankCap]
  have hBmem := main_inverse_deficit_toReal_memLp_lp128_of_ennreal
    Y (inverseBankCap .globalInverse : ℝ) hβ hBank.history_finite hBank.total_L128
  have hsource : ∀ᵐ ω ∂μ, 0 ≤ d ω ∧ d ω ≤ 2 * B ω := by
    simpa [d, Q, σ, x, B, Y] using
      main_actual_inverse_observable_source_history_bounds_of_native_state
        M h hM hg n s hs t ht hpast
  have hB0 : ∀ᵐ ω ∂μ, 0 ≤ B ω := by
    filter_upwards [hsource] with ω hω
    rcases hω with ⟨hd0, hdB⟩
    linarith
  have hBstar0 : ∀ᵐ ω ∂μ, 0 ≤ Bstar ω :=
    Filter.Eventually.of_forall fun ω =>
      (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left 1 (B ω))
  have hBstarMem : MemLp Bstar 128 μ := by
    apply MemLp.mono' ((memLp_const (1 : ℝ)).add hBmem.1)
      hBstarMeas.aestronglyMeasurable
    filter_upwards [hB0] with ω hω
    change ‖max 1 (B ω)‖ ≤ 1 + B ω
    rw [Real.norm_of_nonneg
      ((by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left 1 (B ω)))]
    exact max_le (by linarith) (by norm_num)
  have hdMeas : Measurable d := by
    simpa only [d, Q, σ, x] using main_actual_inverse_observable_measurable M n s t
  have hdBstar : ∀ᵐ ω ∂μ, 0 ≤ d ω ∧ d ω ≤ 2 * Bstar ω := by
    filter_upwards [hsource] with ω hω
    rcases hω with ⟨h0, hupper⟩
    exact ⟨h0, le_trans hupper
      (mul_le_mul_of_nonneg_left (le_max_right 1 (B ω)) (by norm_num))⟩
  exact main_inverse_deficit_trace_integrability_of_lp128
    Bstar d hdMeas hBstarMem hBstar0 hdBstar

/-- The actual global inverse bank also controls the padded history factor
`max 1 B` used by the source-root coefficient comparison. The padding is
absorbed into the bank split because its cap is at least one. -/
theorem main_actual_inverse_deficit_padded_cubic_integral_bound_of_native_state
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (s : ℕ) (hs : 1 ≤ s ∧ s ≤ 40)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hpast : ∀ j < n, nativeInductionState M h j) :
    let Q := originCube 2 n
    let σ := (Annealed.sigmaBar M n : ℝ)
    let x := modelInsertedScalar (closure (cubeSet Q)) (n + (s : ℤ) - 1) t
    ∫ ω,
        (max 1 ((bankFiniteRootHistoryMax (bankLocalRoots Q 5) M n (n + 40)
          (bankPartialInsertionWeights n s t) ω).toReal)) ^ 2 *
          mainInverseObservable n M.nu σ (x ω)
          ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      (inverseBankCap .globalInverse : ℝ) ^ 2 *
          (∫ ω, mainInverseObservable n M.nu σ (x ω)
            ∂(Cutoff.cutoffSampleLaw M).toMeasure) +
        2 * (2 * (inverseBankCap .globalInverse : ℝ) ^ 2 *
              (inverseBankReserve .globalInverse : ℝ) +
            3 * (inverseBankCap .globalInverse : ℝ) *
              (inverseBankReserve .globalInverse : ℝ) ^ 2 +
            (inverseBankReserve .globalInverse : ℝ) ^ 3) := by
  intro Q σ x
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let Y : Cutoff.CutoffSample 2 → ENNReal :=
    bankFiniteRootHistoryMax (bankLocalRoots Q 5) M n (n + 40)
      (bankPartialInsertionWeights n s t)
  let B : Cutoff.CutoffSample 2 → ℝ := fun ω => (Y ω).toReal
  let Bstar : Cutoff.CutoffSample 2 → ℝ := fun ω => max 1 (B ω)
  let d : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    mainInverseObservable n M.nu σ (x ω)
  let R : Cutoff.CutoffSample 2 → ℝ :=
    inverseBankPopulationRemainder .globalInverse (bankLocalRoots Q 5) M n
      (n + 40) (bankPartialInsertionWeights n s t)
  let β : ℝ := inverseBankCap .globalInverse
  let ε : ℝ := inverseBankReserve .globalInverse
  have hBank := main_local_history_global_bank_of_native_state
    M h hM hg n s t ht hpast
  have hYmeas : Measurable Y := history_finite_max_measurable _ _
    (fun Q' => bank_root_inverse_history_measurable Q'.1 M n (n + 40)
      (bankPartialInsertionWeights n s t))
  have hBmeas : Measurable B := by
    exact ENNReal.measurable_toReal.comp hYmeas
  have hBstarMeas : Measurable Bstar := measurable_const.max hBmeas
  have hβ : 1 ≤ β := by norm_num [β, inverseBankCap, inverseBankA,
    inverseBankE]
  have hβ0 : 0 ≤ β := le_trans (by norm_num) hβ
  have hε : 0 ≤ ε := by norm_num [ε, inverseBankReserve]
  have hBmem := main_inverse_deficit_toReal_memLp_lp128_of_ennreal
    Y β hβ0 hBank.history_finite hBank.total_L128
  have hsource : ∀ᵐ ω ∂μ, 0 ≤ d ω ∧ d ω ≤ 2 * B ω := by
    simpa [d, Q, σ, x, B, Y] using
      main_actual_inverse_observable_source_history_bounds_of_native_state
        M h hM hg n s hs t ht hpast
  have hB0 : ∀ᵐ ω ∂μ, 0 ≤ B ω := by
    filter_upwards [hsource] with ω hω
    rcases hω with ⟨hd0, hdB⟩
    linarith
  have hBstar0 : ∀ᵐ ω ∂μ, 0 ≤ Bstar ω :=
    Filter.Eventually.of_forall fun ω =>
      (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left 1 (B ω))
  have hBstarMem : MemLp Bstar 128 μ := by
    apply MemLp.mono' ((memLp_const (1 : ℝ)).add hBmem.1)
      hBstarMeas.aestronglyMeasurable
    filter_upwards [hB0] with ω hω
    change ‖max 1 (B ω)‖ ≤ 1 + B ω
    rw [Real.norm_of_nonneg
      ((by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left 1 (B ω)))]
    exact max_le (by linarith) (by norm_num)
  have hR0 : ∀ ω, 0 ≤ R ω := hBank.remainder_nonneg
  have hBsplit : ∀ᵐ ω ∂μ, Bstar ω ≤ β + R ω := by
    filter_upwards [hBank.history_le] with ω hω
    have hsplit : Y ω ≤ ENNReal.ofReal (β + R ω) := by
      rw [← ENNReal.ofReal_add hβ0 (hR0 ω)] at hω
      simpa [Y, β, R] using hω
    have hreal : B ω ≤ β + R ω := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsplit
      simpa [B, Y, ENNReal.toReal_ofReal (add_nonneg hβ0 (hR0 ω))] using this
    have hpad : 1 ≤ β + R ω := by nlinarith [hβ, hR0 ω]
    exact max_le hpad hreal
  have hdmeas : Measurable d := by
    simpa only [d, Q, σ, x] using main_actual_inverse_observable_measurable M n s t
  have hdB : ∀ᵐ ω ∂μ, 0 ≤ d ω ∧ d ω ≤ 2 * Bstar ω := by
    filter_upwards [hsource] with ω hω
    rcases hω with ⟨h0, hupper⟩
    have hBnonneg : 0 ≤ B ω := by linarith
    exact ⟨by simpa [d, Q, σ, x] using h0,
      le_trans (by simpa [d, Q, σ, x, B, Y] using hupper)
        (mul_le_mul_of_nonneg_left (le_max_right 1 (B ω)) (by norm_num))⟩
  have hRmem : MemLp R 128 μ := by
    rw [memLp_iff]
    exact lt_of_le_of_lt hBank.remainder_L128 ENNReal.ofReal_lt_top
  have hRcap : lpNorm R 128 μ ≤ ε := by
    change (eLpNorm R 128 μ).toReal ≤ ε
    calc
      _ ≤ (ENNReal.ofReal ε).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hBank.remainder_L128
      _ = ε := ENNReal.toReal_ofReal hε
  have hIntegrable := main_inverse_deficit_trace_integrability_of_lp128
    Bstar d hdmeas hBstarMem hBstar0 hdB
  have hbound := main_inverse_deficit_cubic_integral_bound_of_lp128
    β ε Bstar d R hβ0 (Filter.Eventually.of_forall hR0) hBsplit hdB
    hIntegrable.2 hIntegrable.1 hRmem hRcap
  simpa only [μ, β, ε, Bstar, d, R, Y, B, Q, σ, x] using hbound

end ASDExplicitGamma.Main
