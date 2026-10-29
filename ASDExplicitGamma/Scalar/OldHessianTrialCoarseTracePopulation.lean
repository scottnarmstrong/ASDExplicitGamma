module

public import ASDExplicitGamma.Scalar.OldHessianTrialCoarseTraceSeries
public import ASDExplicitGamma.Scalar.OldHessianTrialGroupedLocalReal
public import ASDExplicitGamma.Scalar.OldHessianTrialPhysicalTraceMoments

/-! Exact shifted coarse/fine trace partition and its actual OLD local
bank population payment, with no random-variable substitution. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Cold Algsuperdiff.Section3
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- The shifted child trace averages over the genuine coarse partition
are precisely the original parent's common fine trace average. -/
theorem old_hessian_coarse_fine_trace_partition (Q : TriadicCube 2) (coarse j : ℕ)
    (a : CoeffField 2) :
    oldSignedCellAverage Q coarse (fun D => descendantsAverage D.val (1+j)
      (fun U => traceDefect (openCubeSet U) a 1))=
      descendantsAverage Q (coarse+(1+j)) (fun U => traceDefect (openCubeSet U) a 1) := by
  exact (old_signed_cell_average_eq_descendantsAverage Q coarse
    (fun D => descendantsAverage D (1+j) (fun U => traceDefect (openCubeSet U) a 1))).trans
      (descendantsAverage_add_eq_descendantsAverage_descendantsAverage Q coarse (1+j) _).symm

/-- Every actual shifted coarse series term is paid by the depth-j local
bank and the literal large-parent depth134+j trace. The r4->r5 shift does
not change the local baseline's frame index. -/
theorem old_hessian_actual_coarse_trace_term_bank
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ k<N,nativeInductionState M h k) (m : ℤ) (hm : m<N) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,∀ j : ℕ,
      oldHessianCoarseTraceTerm (originCube 2 (m+129)) 133 M.nu (Annealed.sigmaBar M m)
        (oldHessianOldOpenCoefficient (m+129) m ω) j ≤
      ((inverseBankCap .localInverse:ℝ)*bankDepthFrame M j+oldHessianLocalDepthRare M m j ω)*
        rawWeakTraceSequence M m (originCube 2 (m+129)) 0 ω (134+j) := by
  filter_upwards [old_hessian_actual_coarse_shifted_depth_bank M h hM hg N hpast m hm] with ω hω
  intro j
  let Q := originCube 2 (m+129)
  let k := oldHessianOldOpenCoefficient (m+129) m ω
  let a := responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m) k
  let C := (inverseBankCap .localInverse:ℝ)*bankDepthFrame M j+oldHessianLocalDepthRare M m j ω
  have hEll := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
    M.nu (Annealed.sigmaBar M m) M.nu_pos (Annealed.sigmaBar_characterization M m).1 k
  have hT (D : OldSignedCellIndex Q 133) :
      0≤descendantsAverage D.val (1+j) (fun U => traceDefect (openCubeSet U) a 1) := by
    apply descendantsAverage_nonneg
    intro U hU
    exact Cold.coarse_square_traceDefect_nonneg U
      (hEll.mono (measurableSet_openCubeSet U)
        ((openCubeSet_subset_of_mem_descendantsAtDepth hU).trans
          (openCubeSet_subset_of_mem_descendantsAtDepth D.property)))
  have hh := old_signed_cell_average_mono Q 133 (fun D =>
    mul_le_mul_of_nonneg_right (hω j D.val D.property) (hT D))
  change oldHessianCoarseTraceTerm Q 133 M.nu (Annealed.sigmaBar M m) k j ≤
    oldSignedCellAverage Q 133 (fun D => C*descendantsAverage D.val (1+j)
      (fun U => traceDefect (openCubeSet U) a 1)) at hh
  rw [old_signed_cell_average_mul,old_hessian_coarse_fine_trace_partition,
    show 133+(1+j)=134+j by omega] at hh
  change oldHessianCoarseTraceTerm Q 133 M.nu (Annealed.sigmaBar M m) k j ≤
    C*descendantsAverage (originCube 2 (m+129)) (134+j) (fun U => traceDefect (openCubeSet U)
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m)
        (oldHessianOldOpenCoefficient (m+129) m ω)) 1) at hh
  rw [old_hessian_old_open_trace_sequence] at hh
  exact hh

end
end ASDExplicitGamma.Scalar
