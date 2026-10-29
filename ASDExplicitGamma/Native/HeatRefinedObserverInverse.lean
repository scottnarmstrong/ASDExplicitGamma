module

public import ASDExplicitGamma.Native.ParentBoundaryObserverBandTrace
public import ASDExplicitGamma.Native.GenericSourceBandInverse

/-! The refined observer uses the ORIGINAL parent-frame OLD bank. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic
open ASDExplicitGamma.Response ASDExplicitGamma.Variational
noncomputable section

/-- The actual observer inverse trace is the lower-right block of the parent
band restricted to that observer, with sigma_n kept unchanged. -/
theorem heat_refined_observer_inverse_trace_eq
    (M : ABKModel 2) (q n : ℤ) (r : ℕ)
    (hq : originCube 2 q ∈ descendantsAtDepth (originCube 2 n) r)
    (height : ℕ) (t : ℝ) (ω : Cutoff.CutoffSample 2) :
    bankInverseTraceObservable q M.nu (Annealed.sigmaBar M n) M.nu_pos
      (Annealed.sigmaBar_characterization M n).1
      (parentBoundaryObserverBandScalar q n height t ω) =
    Matrix.trace (coarseBlockMatrix (cubeSet (originCube 2 q))
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n:ℝ)
        (pureFluxOpenResponseRestriction n (nativeSourceBandScalar n height t ω)))).lowerRight := by
  let Q := originCube 2 q
  have hae : responsePlanarCoefficientField M.nu
      (ContinuousMap.linearIsometryBoundedOfCompact (closure (cubeSet Q)) ℝ ℝ
        (parentBoundaryObserverBandScalar q n height t ω)) =ᵐ[volume.restrict (cubeSet Q)]
      attenuatedCoefficient M n (n+(height:ℤ)) (fun _ => Real.sqrt t) ω :=
    (ae_restrict_mem (μ := volume) (measurableSet_cubeSet Q)).mono
      (fun x hx => parent_boundary_observer_band_coefficient_on_cube M q n height t ω x hx)
  have hmat := coarseBlockMatrix_congr_of_ae_eq hae
  rw [native_source_band_coarse_matrix_frame M n height t ω hq,
    bank_inverse_trace_observable_eq]
  dsimp [bankInverseTrace]
  rw [hmat]
  simp only [frameMatrix,Matrix.trace,Matrix.diag_apply,Matrix.smul_apply,smul_eq_mul,Q]

/-- Every observer within the five-level source population is controlled by
the same parent-bank history, hence by the same OLD rare remainder. No extra
frame ratio and no maximum over new descendants is introduced. -/
theorem heat_refined_observer_inverse_ae_le
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (q n : ℤ) (r : ℕ) (hr : r ≤ 5)
    (hq : originCube 2 q ∈ descendantsAtDepth (originCube 2 n) r)
    (height : ℕ) (hpast : ∀ j<n,nativeInductionState M h j) (t : ℝ) (ht : t ≤ 1) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      bankInverseTraceObservable q M.nu (Annealed.sigmaBar M n) M.nu_pos
        (Annealed.sigmaBar_characterization M n).1
        (parentBoundaryObserverBandScalar q n height t ω) ≤
      2*((3683/2500:ℝ)+nativeSourceBandRemainder M n height t ω) := by
  let Q := originCube 2 q
  let σ : ℝ := Annealed.sigmaBar M n
  have hb := native_source_band_history_rare_split M h hM hg n height hpast t ht
  filter_upwards [hb.1,hb.2.2.2.2] with ω hfinite hrare
  let H := pureFluxOpenResponseRestriction n (nativeSourceBandScalar n height t ω)
  let af := responseFramePlanarCoefficientField M.nu σ H
  let A := (coarseBlockMatrix (cubeSet Q) af).lowerRight
  have hEllParent := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet (originCube 2 n))
    M.nu σ M.nu_pos (Annealed.sigmaBar_characterization M n).1 H
  have hEll := hEllParent.mono (measurableSet_openCubeSet Q)
    (openCubeSet_subset_of_mem_descendantsAtDepth hq)
  have hroot := bank_inverse_depth_zero_le_history Q af hEll
    (show 1 < (3:ℝ)^(1/4:ℝ) from Real.one_lt_rpow (by norm_num) (by norm_num))
  have he : lemmaVInverseDepthMax Q af 0=Book.Ch02.matrixNorm A := by
    unfold lemmaVInverseDepthMax
    simp only [descendantsAtDepth_zero,Book.Ch02.finsetSupReal,Finset.coe_singleton,Set.image_singleton,
      csSup_singleton]
    exact congrArg Book.Ch02.matrixNorm (Scalar.inverse_history_lowerRight Q af hEll)
  rw [he] at hroot
  have hh := native_source_band_mesh_history_le M n height t ω r hr hfinite.ne hq
  have h0 := (le_abs_self (A 0 0)).trans (clipped_matrix_entry_abs_le_norm A 0 0)
  have h1 := (le_abs_self (A 1 1)).trans (clipped_matrix_entry_abs_le_norm A 1 1)
  rw [heat_refined_observer_inverse_trace_eq M q n r hq]
  change Matrix.trace A ≤ _
  have htrace : Matrix.trace A ≤ 2*Book.Ch02.matrixNorm A := by
    simp only [Matrix.trace,Fin.sum_univ_two,Matrix.diag_apply,Book.Ch02.matrixNorm]
    linarith only [h0,h1]
  exact htrace.trans (mul_le_mul_of_nonneg_left ((hroot.trans hh).trans hrare) (by norm_num))

end
end ASDExplicitGamma.Native
