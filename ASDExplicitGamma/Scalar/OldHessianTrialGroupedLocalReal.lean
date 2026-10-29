module

public import ASDExplicitGamma.Scalar.OldHessianTrialPhysicalDepthBank
public import ASDExplicitGamma.Scalar.OldHessianTrialGroupedRealBank

/-! Real OLD local depth remainders and the exact coarse shifted-depth
split on the actual large parent. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Algsuperdiff.Section3
open scoped ENNReal
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- The actual grouped local depth remainder, finite on every sample. -/
def oldHessianLocalDepthRare (M : ABKModel 2) (m : ℤ) (j : ℕ)
    (ω : Cutoff.CutoffSample 2) : ℝ := (oldHessianGroupedDepthRare M m j ω).toReal

/-- Real local depth remainders retain their full scalar grouped L128 reserve. -/
theorem old_hessian_actual_local_depth_rare
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ k<N,nativeInductionState M h k) (m : ℤ) (hm : m<N) (j : ℕ) :
    Measurable (oldHessianLocalDepthRare M m j) ∧
    (∀ ω,0≤oldHessianLocalDepthRare M m j ω) ∧
    eLpNorm (oldHessianLocalDepthRare M m j) 128 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (5*inverseBankDepthReserve .localInverse M j) := by
  have hh := old_hessian_grouped_local_depth_bank M h hM hg N hpast m hm j
  have hf : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,oldHessianGroupedDepthRare M m j ω<⊤ :=
    Filter.Eventually.of_forall (fun _ =>
      (Finset.sup_lt_iff (by simp : (⊥:ℝ≥0∞)<⊤)).mpr (fun _ _ => ENNReal.ofReal_lt_top))
  refine ⟨ENNReal.measurable_toReal.comp hh.1,fun _ => ENNReal.toReal_nonneg,?_⟩
  change eLpNorm (fun ω => (oldHessianGroupedDepthRare M m j ω).toReal) 128 _ ≤ _
  rw [←old_hessian_finite_bank_norm _ _ 128 hf]
  exact hh.2.1

/-- The actual coarse r4 inverse block at shifted depth1+j uses the fine
r5 depth-j bank, preserving the exact source baseline and reserve. -/
theorem old_hessian_actual_coarse_shifted_depth_bank
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ k<N,nativeInductionState M h k) (m : ℤ) (hm : m<N) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,∀ j : ℕ,
      ∀ U∈descendantsAtDepth (originCube 2 (m+129)) 133,
      lemmaVInverseDepthMax U
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m)
          (oldHessianOldOpenCoefficient (m+129) m ω)) (1+j) ≤
        (inverseBankCap .localInverse:ℝ)*bankDepthFrame M j+oldHessianLocalDepthRare M m j ω := by
  have hall := ae_all_iff.mpr (fun j =>
    (old_hessian_grouped_local_depth_bank M h hM hg N hpast m hm j).2.2)
  filter_upwards [hall] with ω hω
  intro j U hU
  have hR : oldHessianGroupedDepthRare M m j ω<⊤ :=
    (Finset.sup_lt_iff (by simp : (⊥:ℝ≥0∞)<⊤)).mpr (fun _ _ => ENNReal.ofReal_lt_top)
  have hb : 0≤(inverseBankCap .localInverse:ℝ)*bankDepthFrame M j :=
    mul_nonneg (by norm_num [inverseBankCap]) (bankDepthFrame_pos M j).le
  have hh := (old_hessian_coarse_shifted_depth_ofReal_le_grouped M m ω U hU j).trans (hω j).2
  have hfinite : ENNReal.ofReal ((inverseBankCap .localInverse:ℝ)*bankDepthFrame M j)+
      oldHessianGroupedDepthRare M m j ω ≠ ⊤ :=
    (ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top,hR⟩).ne
  have ht := ENNReal.toReal_mono hfinite hh
  rw [ENNReal.toReal_ofReal (lemmaVInverseDepthMax_nonneg U _ (1+j)),
    ENNReal.toReal_add ENNReal.ofReal_ne_top hR.ne,ENNReal.toReal_ofReal hb] at ht
  exact ht

end
end ASDExplicitGamma.Scalar
