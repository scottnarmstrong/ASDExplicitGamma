module

public import ASDExplicitGamma.Inverse.RawShellBandHeat
public import ASDExplicitGamma.Inverse.RawShellQ3PowerGenerator
public import ASDExplicitGamma.Inverse.ClippedMatrixEntryCap
public import ASDExplicitGamma.Inverse.SourceCovarianceBudget
public import ASDExplicitGamma.Inverse.RawMomentRoot
public import ASDExplicitGamma.Inverse.RawShellBudget
public import ASDExplicitGamma.Gaussian.ModelHeatAverage

/-! Bank-backed finite-p generator rows for deterministic raw shell profiles. -/

@[expose] public section

open MeasureTheory Set Filter
open Homogenization Algsuperdiff.Section3
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Response ASDExplicitGamma.Main
open ASDExplicitGamma.Variational
open scoped ENNReal BigOperators

namespace ASDExplicitGamma.Inverse

/-- The step profile remains bounded by one on the full band when the
prescribed attenuation vector is bounded. -/
theorem raw_shell_band_step_weights_bounds
    (n : ℤ) (N i : ℕ) (hi : i < N) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc n (n + (N : ℤ)), 0 ≤ weights k ∧ weights k ≤ 1)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ∀ k ∈ Finset.Ioc n (n + (N : ℤ)),
      0 ≤ rawShellBandStepWeights n i weights t k ∧
        rawShellBandStepWeights n i weights t k ≤ 1 := by
  intro k hk
  by_cases hcur : k = n + (i : ℤ) + 1
  · subst k
    have hstep : rawShellBandStepWeights n i weights t (n + (i : ℤ) + 1) =
        Real.sqrt t * weights (n + (i : ℤ) + 1) := by
      simp [rawShellBandStepWeights]
    rw [hstep]
    have hwcur := hw (n + (i : ℤ) + 1) hk
    refine ⟨mul_nonneg (Real.sqrt_nonneg _) hwcur.1, ?_⟩
    calc
      Real.sqrt t * weights (n + (i : ℤ) + 1) ≤ 1 * weights (n + (i : ℤ) + 1) :=
        mul_le_mul_of_nonneg_right (Real.sqrt_le_one.mpr ht.2) hwcur.1
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hwcur.2 (by norm_num)
      _ = 1 := by ring
  · by_cases hpast : k ∈ Finset.Ioc n (n + (i : ℤ))
    · have hkN : k ∈ Finset.Ioc n (n + (N : ℤ)) := by
        simp only [Finset.mem_Ioc] at hk hpast ⊢
        have hle : (i : ℤ) ≤ (N : ℤ) := by exact_mod_cast (Nat.le_of_lt hi)
        exact ⟨hpast.1, le_trans hpast.2 (by omega)⟩
      simp [rawShellBandStepWeights, hcur, hpast]
      exact hw k hkN
    · simp [rawShellBandStepWeights, hcur, hpast]

/-- Zero coordinates beyond the current insertion leave the scalar profile
unchanged when it is viewed at the total band endpoint. -/
theorem raw_shell_band_step_scalar_zero_tail
    (M : ABKModel 2) (n : ℤ) (N i : ℕ) (hi : i < N)
    (weights : ℤ → ℝ) (t : ℝ) (ω : CutoffSample 2) :
    rawShellBandScalarFromWeights M n N (rawShellBandStepWeights n i weights t) ω =
      rawShellBandScalarFromWeights M n (i + 1)
        (rawShellBandStepWeights n i weights t) ω := by
  classical
  let K := closure (cubeSet (originCube 2 n))
  have hsub : Finset.Ioc n (n + ((i + 1 : ℕ) : ℤ)) ⊆
      Finset.Ioc n (n + (N : ℤ)) := by
    intro k hk
    simp only [Finset.mem_Ioc] at hk ⊢
    have hle : (i : ℤ) ≤ (N : ℤ) := by exact_mod_cast (Nat.le_of_lt hi)
    omega
  have hsum :
      (∑ k ∈ Finset.Ioc n (n + (N : ℤ)),
        rawShellBandStepWeights n i weights t k • shellFieldScalarRestriction K (ω.1 k)) =
      ∑ k ∈ Finset.Ioc n (n + ((i + 1 : ℕ) : ℤ)),
        rawShellBandStepWeights n i weights t k • shellFieldScalarRestriction K (ω.1 k) := by
    apply (Finset.sum_subset hsub ?_).symm
    intro k hk hkn
    have hcur : k ≠ n + (i : ℤ) + 1 := by
      intro heq
      subst k
      apply hkn
      simp only [Finset.mem_Ioc]
      omega
    have hprefix : k ∉ Finset.Ioc n (n + (i : ℤ)) := by
      intro hp
      apply hkn
      simp only [Finset.mem_Ioc] at hp ⊢
      omega
    simp [rawShellBandStepWeights, hcur, hprefix]
  ext x
  simp only [rawShellBandScalarFromWeights, ContinuousMap.add_apply,
    ContinuousMap.sum_apply, ContinuousMap.smul_apply]
  have hsumx := congrArg (fun f : C(K, ℝ) => f x) hsum
  simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply] at hsumx
  rw [hsumx]

private theorem raw_shell_band_symmPart (M : ABKModel 2) (n J : ℤ)
    (weights : ℤ → ℝ) (ω : CutoffSample 2) (x : Vec 2) :
    Homogenization.symmPart (attenuatedCoefficient M n J weights ω x) =
      M.nu • (1 : Mat 2) := by
  classical
  unfold attenuatedCoefficient
  have hsum : Homogenization.symmPart
      (∑ k ∈ Finset.Ioc n J, weights k • (ω.val k).forgetShell x) = 0 := by
    ext i j
    simp only [Homogenization.symmPart, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul, ShellField.forgetShell_apply]
    rw [← Finset.sum_add_distrib]
    apply (div_eq_zero_iff).mpr
    left
    apply Finset.sum_eq_zero
    intro k hk
    rw [(ω.val k).skew_entry x i j]
    ring
  have hadd (A B : Mat 2) : Homogenization.symmPart (A + B) =
      Homogenization.symmPart A + Homogenization.symmPart B := by
    ext i j
    simp only [Homogenization.symmPart, Matrix.add_apply]
    ring
  rw [hadd, Cutoff.symmPart_coefficientCutoff, hsum]
  simp

/-- The weighted scalar field is exactly the `(1,0)` entry of its actual
attenuated coefficient. -/
theorem raw_shell_band_scalar_eq_entry
    (M : ABKModel 2) (n : ℤ) (s : ℕ) (weights : ℤ → ℝ)
    (ω : CutoffSample 2) (ell : ℤ)
    (hK : closure (cubeSet (originCube 2 n)) ⊆ openCubeSet (originCube 2 ell))
    (x : closure (cubeSet (originCube 2 n))) :
    rawShellBandScalarFromWeights M n s weights ω x =
      attenuatedCoefficient M n (n + (s : ℤ)) weights ω x.1 1 0 := by
  classical
  have hold := olderField_apply_eq_coefficientCutoff
    (closure (cubeSet (originCube 2 n))) M ell n hK ω x
  have hsum :
      (∑ k ∈ Finset.Ioc n (n + (s : ℤ)),
        weights k • shellFieldScalarRestriction
          (closure (cubeSet (originCube 2 n))) (ω.val k)) x =
      (∑ k ∈ Finset.Ioc n (n + (s : ℤ)),
        weights k • (ω.val k).forgetShell x.1) 1 0 := by
    simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply,
      Matrix.sum_apply, Matrix.smul_apply]
    apply Finset.sum_congr rfl
    intro k hk
    simp [shellFieldScalarRestriction, planarShellScalarStream,
      planarShellMatrixEntry, ShellField.forgetShell_apply]
  rw [rawShellBandScalarFromWeights, ContinuousMap.add_apply, hold, hsum]
  simp only [attenuatedCoefficient, Matrix.add_apply,
    Cutoff.coefficientCutoff_apply]

/-- The actual inverse-trace observable is the trace of the lower-right block
in the true fixed frame. -/
theorem raw_shell_band_bank_inverse_trace_eq_frame_trace
    (M : ABKModel 2) (n : ℤ)
    (x : C(closure (cubeSet (originCube 2 n)), ℝ)) :
    bankInverseTraceObservable n M.nu (Annealed.sigmaBar M n : ℝ)
        M.nu_pos (Annealed.sigmaBar_characterization M n).1 x =
      Matrix.trace ((frameMatrix (Annealed.sigmaBar M n : ℝ)
        (coarseBlockMatrix (cubeSet (originCube 2 n))
          (responsePlanarCoefficientField M.nu
            (ContinuousMap.linearIsometryBoundedOfCompact
              (closure (cubeSet (originCube 2 n))) ℝ ℝ x)))).lowerRight) := by
  let K := closure (cubeSet (originCube 2 n))
  let σ : ℝ := Annealed.sigmaBar M n
  change bankInverseTraceObservable n M.nu σ M.nu_pos
      (Annealed.sigmaBar_characterization M n).1 x =
    Matrix.trace ((frameMatrix σ
      (coarseBlockMatrix (cubeSet (originCube 2 n))
        (responsePlanarCoefficientField M.nu
          (ContinuousMap.linearIsometryBoundedOfCompact K ℝ ℝ x)))).lowerRight)
  rw [bank_inverse_trace_observable_eq n M.nu σ M.nu_pos
    (Annealed.sigmaBar_characterization M n).1 x]
  simp [K, σ, bankInverseTrace, frameMatrix, Matrix.trace,
    Fin.sum_univ_two, Matrix.diag_apply]

/-- The full-response trace at the total band endpoint is the fixed-frame
model trace of the current coordinate profile plus four. -/
theorem raw_shell_band_step_trace_eq
    (M : ABKModel 2) (n : ℤ) (N i : ℕ) (hi : i < N)
    (weights : ℤ → ℝ) (t : ℝ) (ω : CutoffSample 2) :
    rootTraceObservable M (originCube 2 n) n (n + (N : ℤ)) n
        (rawShellBandStepWeights n i weights t) ω =
      modelTraceObservable n M.nu (Annealed.sigmaBar M n : ℝ)
        (rawShellBandScalarFromWeights M n (i + 1)
          (rawShellBandStepWeights n i weights t) ω) + 4 := by
  classical
  let Q := originCube 2 n
  let K := closure (cubeSet Q)
  let σ : ℝ := Annealed.sigmaBar M n
  let W := rawShellBandStepWeights n i weights t
  let J := n + (N : ℤ)
  let J₀ := n + ((i + 1 : ℕ) : ℤ)
  let x := rawShellBandScalarFromWeights M n (i + 1) W ω
  obtain ⟨ell, hK⟩ := exists_originCube_containing_compact K
    (isBounded_cubeSet Q).isCompact_closure
  have hzeroTail := raw_shell_band_step_scalar_zero_tail M n N i hi weights t ω
  have hentryFull := raw_shell_band_scalar_eq_entry M n N W ω ell hK
  have hentryStep := raw_shell_band_scalar_eq_entry M n (i + 1) W ω ell hK
  have hentry (y : K) :
      attenuatedCoefficient M n J W ω y.1 1 0 =
        attenuatedCoefficient M n J₀ W ω y.1 1 0 := by
    have he := congrArg (fun f : C(K, ℝ) => f y) hzeroTail
    rw [hentryFull, hentryStep] at he
    exact he
  have hphysical : ∀ y ∈ cubeSet Q,
      responsePlanarCoefficientField M.nu
        (ContinuousMap.linearIsometryBoundedOfCompact K ℝ ℝ x) y =
      attenuatedCoefficient M n J W ω y := by
    intro y hy
    rw [responsePlanarCoefficientField, responseCoefficientExtension_eq _ hy,
      ContinuousMap.linearIsometryBoundedOfCompact_apply_apply]
    let yK : K := ⟨y, subset_closure hy⟩
    have hscalar := hentryStep yK
    have hmat := raw_shell_band_symmPart M n J W ω y
    have hmat' := planar_coefficient_eq_of_symmPart M.nu
      (attenuatedCoefficient M n J W ω y) hmat
    have hxy : x yK = attenuatedCoefficient M n J W ω y 1 0 := by
      dsimp [x]
      exact hscalar.trans (hentry yK).symm
    rw [hxy]
    exact hmat'
  have hae := (ae_restrict_mem (μ := volume) (measurableSet_cubeSet Q)).mono
    (fun y hy => hphysical y hy)
  have hdef : modelTraceObservable n M.nu σ x =
      traceDefect (cubeSet Q) (attenuatedCoefficient M n J W ω) σ := by
    unfold modelTraceObservable traceDefect
    rw [coarseBlockMatrix_congr_of_ae_eq hae]
  calc
    rootTraceObservable M Q n J n W ω =
        traceDefect (cubeSet Q) (attenuatedCoefficient M n J W ω) σ + 4 :=
      root_trace_observable_eq_trace_defect M Q n J n W ω
    _ = modelTraceObservable n M.nu σ x + 4 := by rw [← hdef]

/-- The fixed-frame inverse trace during a coordinate step is bounded by the
exact local bank history for that weighted prefix. -/
theorem raw_shell_band_step_inverse_trace_le_local_history
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (N i : ℕ) (hi : i < N)
    (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc n (n + (N : ℤ)),
      0 ≤ weights k ∧ weights k ≤ 1)
    (hpast : ∀ j < n, nativeInductionState M h j)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      bankInverseTraceObservable n M.nu (Annealed.sigmaBar M n : ℝ)
        M.nu_pos (Annealed.sigmaBar_characterization M n).1
        (rawShellBandScalarFromWeights M n (i + 1)
          (rawShellBandStepWeights n i weights t) ω) ≤
      2 * rawShellWeightedLocalHistory M n (n + ((i + 1 : ℕ) : ℤ))
        (rawShellBandStepWeights n i weights t) ω := by
  classical
  let Q := originCube 2 n
  let K := closure (cubeSet Q)
  let σ : ℝ := Annealed.sigmaBar M n
  let s := i + 1
  let J := n + (s : ℤ)
  let W := rawShellBandStepWeights n i weights t
  let X := rawShellBandScalarFromWeights M n s W
  let P := rawShellWeightedLocalHistory M n J W
  let k (ω : CutoffSample 2) := pureFluxOpenResponseRestriction n (X ω)
  let kClosed (ω : CutoffSample 2) : ResponseCoefficient (cubeSet Q) :=
    ContinuousMap.linearIsometryBoundedOfCompact K ℝ ℝ (X ω)
  let af (ω : CutoffSample 2) := responseFramePlanarCoefficientField M.nu σ (k ω)
  let A (ω : CutoffSample 2) := coarseBlockMatrix (cubeSet Q) (af ω)
  let D (ω : CutoffSample 2) := bankInverseTraceObservable n M.nu σ M.nu_pos
      (Annealed.sigmaBar_characterization M n).1 (X ω)
  have hstepBounds := raw_shell_band_step_weights_bounds n N i hi weights hw t ht
  have hW : ∀ k ∈ Finset.Ioc n J, 0 ≤ W k ∧ W k ≤ 1 := by
    intro k hk
    apply hstepBounds k
    simp only [Finset.mem_Ioc] at hk ⊢
    exact ⟨hk.1, by dsimp [J, s] at hk ⊢; omega⟩
  have hbank := raw_shell_weighted_local_inverse_bank M h hM hg n J
    (by dsimp [J, s]; omega) W hW hpast
  have hEll (ω : CutoffSample 2) :
      IsEllipticFieldOn (M.nu / σ) (((M.nu / σ) ^ 2 +
        (‖k ω‖ / σ) ^ 2) / (M.nu / σ)) (openCubeSet Q) (af ω) :=
    responseFramePlanarCoefficientField_isElliptic
      (measurableSet_openCubeSet Q) M.nu σ M.nu_pos
      (Annealed.sigmaBar_characterization M n).1 (k ω)
  have hdepthZero (ω : CutoffSample 2) :
      lemmaVInverseDepthMax Q (af ω) 0 = Book.Ch02.matrixNorm (A ω).lowerRight := by
    unfold lemmaVInverseDepthMax
    simp only [descendantsAtDepth_zero, Book.Ch02.finsetSupReal,
      Finset.coe_singleton, Set.image_singleton, csSup_singleton]
    exact congrArg Book.Ch02.matrixNorm
      (Scalar.inverse_history_lowerRight Q (af ω) (hEll ω))
  have hframe (ω : CutoffSample 2) :
      A ω = frameMatrix σ (coarseBlockMatrix (cubeSet Q)
        (responsePlanarCoefficientField M.nu (kClosed ω))) :=
    calc
      A ω = coarseBlockMatrix (cubeSet Q)
          (responseFramePlanarCoefficientField M.nu σ (kClosed ω)) := by
        change coarseBlockMatrix (cubeSet Q) (af ω) = _
        have hae : af ω =ᵐ[volume.restrict (openCubeSet Q)]
            responseFramePlanarCoefficientField M.nu σ (kClosed ω) := by
          filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with y hy
          change responseFramePlanarCoefficientField M.nu σ (k ω) y = _
          rw [responseFramePlanarCoefficientField_apply,
            responseFramePlanarCoefficientField_apply,
            pureFluxOpenResponseRestriction_value n (X ω) hy]
          rw [responseCoefficientExtension_eq (kClosed ω)
            (openCubeSet_subset_cubeSet Q hy),
            ContinuousMap.linearIsometryBoundedOfCompact_apply_apply]
        rw [coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube Q,
          coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube Q]
        exact coarseBlockMatrix_congr_of_ae_eq hae
      _ = frameMatrix σ (coarseBlockMatrix (cubeSet Q)
          (responsePlanarCoefficientField M.nu (kClosed ω))) :=
        response_coarseMatrix_frame_eq (Q := Q) (measurableSet_cubeSet Q)
          M.nu σ M.nu_pos (Annealed.sigmaBar_characterization M n).1 (kClosed ω)
  have hDframe (ω : CutoffSample 2) : D ω = Matrix.trace (A ω).lowerRight := by
    have h := raw_shell_band_bank_inverse_trace_eq_frame_trace M n (X ω)
    dsimp [D, A, Q, σ, X] at h ⊢
    rw [h]
    rw [← hframe ω]
  have htraceNorm (ω : CutoffSample 2) :
      Matrix.trace (A ω).lowerRight ≤ 2 * Book.Ch02.matrixNorm (A ω).lowerRight := by
    let B := (A ω).lowerRight
    have h0 := (le_abs_self (B 0 0)).trans (clipped_matrix_entry_abs_le_norm B 0 0)
    have h1 := (le_abs_self (B 1 1)).trans (clipped_matrix_entry_abs_le_norm B 1 1)
    have h0' : B 0 0 ≤ Book.Ch02.matrixNorm B := by
      simpa only [Book.Ch02.matrixNorm_eq_matrixOperatorNorm,
        Book.Ch02.matrixOperatorNorm] using h0
    have h1' : B 1 1 ≤ Book.Ch02.matrixNorm B := by
      simpa only [Book.Ch02.matrixNorm_eq_matrixOperatorNorm,
        Book.Ch02.matrixOperatorNorm] using h1
    simp only [Matrix.trace, Fin.sum_univ_two]
    dsimp [B]
    nlinarith only [h0', h1']
  have hdepth (ω : CutoffSample 2) :
      lemmaVInverseDepthMax Q (af ω) 0 ≤ lemmaVInverseHistory Q (af ω)
        ((3 : ℝ) ^ (1 / 4 : ℝ)) := by
    exact bank_inverse_depth_zero_le_history Q (af ω) (hEll ω)
      (show 1 < (3 : ℝ) ^ (1 / 4 : ℝ) from
        Real.one_lt_rpow (by norm_num) (by norm_num))
  have hroot : Q ∈ descendantsAtDepth Q 0 := by simp
  filter_upwards [hbank.history_finite] with ω hfinite
  have hmesh := raw_shell_weighted_source_mesh_history_le M n s (by omega)
    W ω 0 (by omega) (ne_of_lt hfinite) hroot
  have hP : lemmaVInverseHistory Q (af ω) ((3 : ℝ) ^ (1 / 4 : ℝ)) ≤ P ω := by
    change lemmaVInverseHistory Q (af ω) ((3 : ℝ) ^ (1 / 4 : ℝ)) ≤
      (bankFiniteRootHistoryMax (bankLocalRoots Q 5) M n J W ω).toReal
    simpa only [af, k, X, s, J] using hmesh
  calc
    D ω = Matrix.trace (A ω).lowerRight := hDframe ω
    _ ≤ 2 * Book.Ch02.matrixNorm (A ω).lowerRight := htraceNorm ω
    _ = 2 * lemmaVInverseDepthMax Q (af ω) 0 := by rw [hdepthZero ω]
    _ ≤ 2 * lemmaVInverseHistory Q (af ω) ((3 : ℝ) ^ (1 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left (hdepth ω) (by norm_num)
    _ ≤ 2 * P ω := mul_le_mul_of_nonneg_left hP (by norm_num)

end ASDExplicitGamma.Inverse
