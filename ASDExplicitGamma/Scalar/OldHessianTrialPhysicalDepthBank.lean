module

public import ASDExplicitGamma.Scalar.OldHessianTrialGroupedDepthBank
public import ASDExplicitGamma.Scalar.OldHessianTrialGroupedHistoryAdapter

/-! Literal inverse blocks, rather than complete histories, at every weak
depth of the actual large-parent source cells. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Algsuperdiff.Section3
open scoped ENNReal
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- Actual framed inverse depth maxima equal the bank's physical block
maxima, with the OLD cutoff independent of the containing parent scale. -/
theorem old_hessian_physical_depth_max (M : ABKModel 2) (n m : ℤ)
    (ω : Cutoff.CutoffSample 2) (U : TriadicCube 2)
    (hU : openCubeSet U ⊆ openCubeSet (originCube 2 n)) (j : ℕ) :
    bankFiniteRootResponseMax (descendantsAtDepth U j) M m (m+40)
      (bankPartialInsertionWeights m 1 0) ω =
      ENNReal.ofReal (lemmaVInverseDepthMax U
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m)
          (oldHessianOldOpenCoefficient n m ω)) j) := by
  have hmax := bank_finite_max_ofReal (descendantsAtDepth U j) (descendantsAtDepth_nonempty U j)
    (fun R => rootInverseResponse M R m (m+40) (bankPartialInsertionWeights m 1 0) ω)
  change bankFiniteRootResponseMax (descendantsAtDepth U j) M m (m+40)
    (bankPartialInsertionWeights m 1 0) ω = _ at hmax
  rw [hmax]
  apply congrArg ENNReal.ofReal
  apply Book.Ch02.finsetSupReal_congr
  intro R hR
  let af := responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m)
    (oldHessianOldOpenCoefficient n m ω)
  have hEll := (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet (originCube 2 n))
    M.nu (Annealed.sigmaBar M m) M.nu_pos (Annealed.sigmaBar_characterization M m).1
      (oldHessianOldOpenCoefficient n m ω)).mono (measurableSet_openCubeSet R)
      ((openCubeSet_subset_of_mem_descendantsAtDepth hR).trans hU)
  rw [inverse_history_lowerRight R af hEll,
    coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube R,
    old_hessian_old_open_coarse_frame M n m ω R
      ((openCubeSet_subset_of_mem_descendantsAtDepth hR).trans hU)]
  change rootInverseResponse M R m (m+40) (bankPartialInsertionWeights m 1 0) ω=
    Book.Ch02.matrixNorm ((Annealed.sigmaBar M m:ℝ) •
      (coarseBlockMatrix (cubeSet R) (Cutoff.coefficientCutoff M.nu m ω).toFun).lowerRight)
  rw [inverse_history_matrixNorm_smul _ _ (Annealed.sigmaBar_characterization M m).1.le]
  simp only [rootInverseResponse,old_hessian_bank_old_coefficient,Book.Ch02.matrixNorm]

/-- Monotonicity of finite maxima over the actual subtype populations. -/
theorem old_hessian_finite_subtype_max_mono {I : Type*} (s t : Finset I)
    (hst : s⊆t) (f : I → ℝ≥0∞) :
    (Finset.univ : Finset ↥s).sup (fun i => f i.val) ≤
      (Finset.univ : Finset ↥t).sup (fun i => f i.val) := by
  classical
  apply Finset.sup_le
  intro i _
  exact Finset.le_sup (f := fun k : ↥t => f k.val)
    (Finset.mem_univ (⟨i.val,hst i.property⟩ : ↥t))

/-- Every actual source-cell depth maximum lies below the corresponding
large-parent grouped block maximum. This inequality is ENNReal-valued. -/
theorem old_hessian_source_depth_ofReal_le_grouped (M : ABKModel 2) (m : ℤ)
    (ω : Cutoff.CutoffSample 2) (r : ℕ) (hr : r≤5)
    (U : TriadicCube 2) (hU : U∈descendantsAtDepth (originCube 2 (m+129)) (129+r)) (j : ℕ) :
    ENNReal.ofReal (lemmaVInverseDepthMax U
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m)
        (oldHessianOldOpenCoefficient (m+129) m ω)) j) ≤
      oldHessianGroupedDepthBlocks M m j ω := by
  classical
  rw [←old_hessian_physical_depth_max M (m+129) m ω U
    (openCubeSet_subset_of_mem_descendantsAtDepth hU) j]
  obtain ⟨D,hD,hUD⟩ := old_hessian_source_cell_observer m r hr U hU
  have hsub : descendantsAtDepth U j ⊆ bankObserverDepthRootUnion D 5 j := by
    intro V hV
    obtain ⟨r0,hr0,hroot⟩ := Finset.mem_biUnion.mp hUD
    exact Finset.mem_biUnion.mpr ⟨r0,hr0,bank_observer_depth_roots_mem D r0 j hroot hV⟩
  have hlocal : bankFiniteRootResponseMax (descendantsAtDepth U j) M m (m+40)
      (bankPartialInsertionWeights m 1 0) ω ≤
      bankFiniteRootResponseMax (bankObserverDepthRootUnion D 5 j) M m (m+40)
        (bankPartialInsertionWeights m 1 0) ω := by
    exact old_hessian_finite_subtype_max_mono _ _ hsub
      (fun V => ENNReal.ofReal (rootInverseResponse M V m (m+40)
        (bankPartialInsertionWeights m 1 0) ω))
  exact hlocal.trans (Finset.le_sup (f := fun D =>
    bankFiniteRootResponseMax (bankObserverDepthRootUnion D 5 j) M m (m+40)
      (bankPartialInsertionWeights m 1 0) ω) hD)

/-- A coarse r4 cell at shifted depth 1+j belongs to the r5 population
at depth j. This exact shift preserves alpha² without an extra frame factor. -/
theorem old_hessian_coarse_shifted_depth_ofReal_le_grouped
    (M : ABKModel 2) (m : ℤ) (ω : Cutoff.CutoffSample 2)
    (U : TriadicCube 2) (hU : U∈descendantsAtDepth (originCube 2 (m+129)) 133) (j : ℕ) :
    ENNReal.ofReal (lemmaVInverseDepthMax U
      (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m)
        (oldHessianOldOpenCoefficient (m+129) m ω)) (1+j)) ≤
      oldHessianGroupedDepthBlocks M m j ω := by
  classical
  rw [←old_hessian_physical_depth_max M (m+129) m ω U
    (openCubeSet_subset_of_mem_descendantsAtDepth hU) (1+j)]
  obtain ⟨D,hD,hUD⟩ := exists_descendant_ancestor_at_depth 89 44 hU
  have hsub : descendantsAtDepth U (1+j) ⊆ bankObserverDepthRootUnion D 5 j := by
    intro V hV
    apply Finset.mem_biUnion.mpr
    refine ⟨5,Finset.mem_range.mpr (by omega),?_⟩
    have ht := mem_descendantsAtDepth_add hUD hV
    change V∈descendantsAtDepth D (40+5+j)
    rw [show 40+5+j=44+(1+j) by omega]
    exact ht
  have hlocal : bankFiniteRootResponseMax (descendantsAtDepth U (1+j)) M m (m+40)
      (bankPartialInsertionWeights m 1 0) ω ≤
      bankFiniteRootResponseMax (bankObserverDepthRootUnion D 5 j) M m (m+40)
        (bankPartialInsertionWeights m 1 0) ω :=
    old_hessian_finite_subtype_max_mono _ _ hsub
      (fun V => ENNReal.ofReal (rootInverseResponse M V m (m+40)
        (bankPartialInsertionWeights m 1 0) ω))
  exact hlocal.trans (Finset.le_sup (f := fun D =>
    bankFiniteRootResponseMax (bankObserverDepthRootUnion D 5 j) M m (m+40)
      (bankPartialInsertionWeights m 1 0) ω) hD)

/-- On a common event, every physical source cell at r0..r5 and every weak
depth is controlled by the unchanged local baseline and the grouped rare part. -/
theorem old_hessian_actual_depth_blocks_le_bank
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ k<N,nativeInductionState M h k) (m : ℤ) (hm : m<N) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,∀ j r : ℕ,r≤5 →
      ∀ U∈descendantsAtDepth (originCube 2 (m+129)) (129+r),
      lemmaVInverseDepthMax U
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m)
          (oldHessianOldOpenCoefficient (m+129) m ω)) j ≤
        (inverseBankCap .localInverse:ℝ)*bankDepthFrame M j+
          (oldHessianGroupedDepthRare M m j ω).toReal := by
  have hall := ae_all_iff.mpr (fun j =>
    (old_hessian_grouped_local_depth_bank M h hM hg N hpast m hm j).2.2)
  filter_upwards [hall] with ω hω
  intro j r hr U hU
  have hR : oldHessianGroupedDepthRare M m j ω<⊤ :=
    (Finset.sup_lt_iff (by simp : (⊥:ℝ≥0∞)<⊤)).mpr (fun _ _ => ENNReal.ofReal_lt_top)
  have hb : 0≤(inverseBankCap .localInverse:ℝ)*bankDepthFrame M j := by
    unfold bankDepthFrame
    exact mul_nonneg (by norm_num [inverseBankCap]) (Real.rpow_nonneg (by norm_num) _)
  have hh := (old_hessian_source_depth_ofReal_le_grouped M m ω r hr U hU j).trans (hω j).2
  have hfinite : ENNReal.ofReal ((inverseBankCap .localInverse:ℝ)*bankDepthFrame M j)+
      oldHessianGroupedDepthRare M m j ω ≠ ⊤ :=
    (ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top,hR⟩).ne
  have ht := ENNReal.toReal_mono hfinite hh
  rw [ENNReal.toReal_ofReal (lemmaVInverseDepthMax_nonneg U _ j),
    ENNReal.toReal_add ENNReal.ofReal_ne_top hR.ne,ENNReal.toReal_ofReal hb] at ht
  exact ht

end
end ASDExplicitGamma.Scalar
