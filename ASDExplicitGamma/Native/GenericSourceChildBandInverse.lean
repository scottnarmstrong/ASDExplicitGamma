module

public import ASDExplicitGamma.Native.GenericSourceChildBandHistory
public import ASDExplicitGamma.Native.GenericSourceActualInverse

/-! Actual inverse-trace domination by the complete normalized local history
on the simultaneous source path. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic ASDExplicitGamma.Response
open ASDExplicitGamma.Variational
noncomputable section

/-- The actual inverse trace is the lower-right trace of the normalized
source coefficient, whose full history is controlled by the bank. -/
theorem native_source_child_band_inverse_trace_eq
    (M : ABKModel 2) (n : ℤ) (height : ℕ) (t : ℝ) (ω : Cutoff.CutoffSample 2) :
    bankInverseTraceObservable (n-1) M.nu (Annealed.sigmaBar M n) M.nu_pos
      (Annealed.sigmaBar_characterization M n).1 (nativeSourceChildBandScalar n height t ω) =
      Matrix.trace (coarseBlockMatrix (cubeSet (originCube 2 (n-1)))
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n:ℝ)
          (pureFluxOpenResponseRestriction (n-1) (nativeSourceChildBandScalar n height t ω)))).lowerRight := by
  let Q := originCube 2 (n-1)
  have hae : responsePlanarCoefficientField M.nu
      (ContinuousMap.linearIsometryBoundedOfCompact (closure (cubeSet Q)) ℝ ℝ
        (nativeSourceChildBandScalar n height t ω)) =ᵐ[volume.restrict (cubeSet Q)]
      attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) ω :=
    (ae_restrict_mem (μ := volume) (measurableSet_cubeSet Q)).mono
      (fun x hx => native_source_child_band_coefficient_on_cube M n height t ω x hx)
  have hmat := coarseBlockMatrix_congr_of_ae_eq hae
  have hframe := native_source_child_band_coarse_matrix_frame M n height t ω
    (R := Q) (d := 0) (by simp only [descendantsAtDepth_zero,Finset.mem_singleton]; rfl)
  rw [hframe,bank_inverse_trace_observable_eq]
  dsimp [bankInverseTrace]
  rw [hmat]
  simp only [frameMatrix,Matrix.trace,Matrix.diag_apply,Matrix.smul_apply,smul_eq_mul]

/-- On the bank's true finiteness event the actual inverse trace is at most
twice its complete local majorant, uniformly over the simultaneous band. -/
theorem native_source_child_band_inverse_trace_ae_le
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (height : ℕ)
    (hpast : ∀ j < n, nativeInductionState M h j) (t : ℝ) (ht1 : t ≤ 1) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      bankInverseTraceObservable (n-1) M.nu (Annealed.sigmaBar M n) M.nu_pos
        (Annealed.sigmaBar_characterization M n).1 (nativeSourceChildBandScalar n height t ω) ≤
          2*(nativeSourceChildBandHistory M n height t ω).toReal := by
  let Q := originCube 2 (n-1)
  let σ : ℝ := Annealed.sigmaBar M n
  have hb := native_source_child_band_local_bank M h hM hg n height hpast t ht1
  filter_upwards [hb.history_finite] with ω hfinite
  let H := pureFluxOpenResponseRestriction (n-1) (nativeSourceChildBandScalar n height t ω)
  let af := responseFramePlanarCoefficientField M.nu σ H
  let A := (coarseBlockMatrix (cubeSet Q) af).lowerRight
  have hEll := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
    M.nu σ M.nu_pos (Annealed.sigmaBar_characterization M n).1 H
  have hroot := bank_inverse_depth_zero_le_history Q af hEll
    (show 1 < (3:ℝ)^(1/4:ℝ) from Real.one_lt_rpow (by norm_num) (by norm_num))
  have he : lemmaVInverseDepthMax Q af 0=Book.Ch02.matrixNorm A := by
    unfold lemmaVInverseDepthMax
    simp only [descendantsAtDepth_zero,Book.Ch02.finsetSupReal,Finset.coe_singleton,Set.image_singleton,
      csSup_singleton]
    exact congrArg Book.Ch02.matrixNorm (Scalar.inverse_history_lowerRight Q af hEll)
  rw [he] at hroot
  have hh := native_source_child_band_mesh_history_le M n height t ω 0 (by norm_num) hfinite.ne
    (U := Q) (by simp only [descendantsAtDepth_zero,Finset.mem_singleton]; rfl)
  have h0 := (le_abs_self (A 0 0)).trans (clipped_matrix_entry_abs_le_norm A 0 0)
  have h1 := (le_abs_self (A 1 1)).trans (clipped_matrix_entry_abs_le_norm A 1 1)
  rw [native_source_child_band_inverse_trace_eq]
  change Matrix.trace A ≤ _
  have htrace : Matrix.trace A ≤ 2*Book.Ch02.matrixNorm A := by
    simp only [Matrix.trace,Fin.sum_univ_two,Matrix.diag_apply,Book.Ch02.matrixNorm]
    linarith only [h0,h1]
  exact htrace.trans (mul_le_mul_of_nonneg_left (hroot.trans hh) (by norm_num))

end
end ASDExplicitGamma.Native
