module

public import ASDExplicitGamma.Scalar.RefSplit
public import ASDExplicitGamma.Scalar.DefectOldMaximizerDirSeries
public import ASDExplicitGamma.Scalar.PairFinalId

/-! Budgets for the corrected defect: the OLD inverse history bound for the inner part and the
pathwise inner budget in terms of the flux-affine directional series. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
  ASDExplicitGamma.Native
open Algsuperdiff.Section3
open scoped BigOperators

attribute [local irreducible] Homogenization.descendantsAtDepth

noncomputable section

theorem hist_congr_ae (U : TriadicCube 2) (a a' : CoeffField 2) (q : ℝ) {lam Lam lam' Lam' : ℝ}
    (ha : IsEllipticFieldOn lam Lam (openCubeSet U) a)
    (ha' : IsEllipticFieldOn lam' Lam' (openCubeSet U) a')
    (h : a =ᵐ[volumeMeasureOn (openCubeSet U)] a') :
    lemmaVInverseHistory U a q = lemmaVInverseHistory U a' q := by
  have hd : ∀ k, lemmaVInverseDepthMax U a k = lemmaVInverseDepthMax U a' k := by
    intro k
    unfold lemmaVInverseDepthMax
    apply Book.Ch02.finsetSupReal_congr
    intro R hR
    apply congrArg Book.Ch02.matrixNorm
    have hRU := openCubeSet_subset_of_mem_descendantsAtDepth hR
    have haR := ha.mono (measurableSet_openCubeSet R) hRU
    have haR' := ha'.mono (measurableSet_openCubeSet R) hRU
    rw [Scalar.inverse_history_lowerRight R a haR, Scalar.inverse_history_lowerRight R a' haR']
    rw [Variational.cube_coarseMatrix_eq_open R a, Variational.cube_coarseMatrix_eq_open R a']
    rw [coarseBlockMatrix_congr_of_ae_eq (ae_mono (Measure.restrict_mono_set volume hRU) h)]
  unfold lemmaVInverseHistory
  simp only [hd]

/-- The OLD inverse history of a depth-134 cell of the global coefficient is at most `bhist`. -/
theorem hist_le_Bhist (M : ABKModel 2) (m : ℤ) (Q U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth Q 134) (ω : Cutoff.CutoffSample 2) :
    lemmaVInverseHistory U (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M m : ℝ)
      (oldCutoffSkewCoefficient m Q ω)) ((3 : ℝ) ^ (1 / 4 : ℝ)) ≤ bhist M m Q 134 ω := by
  have h := smooth_feedback_source_history_maximum_member_le Q 134 M.nu
    (Annealed.sigmaBar M m : ℝ) (oldCutoffSkewCoefficient m Q ω) U hU
  refine le_trans (le_of_eq ?_) h
  have hσ : 0 < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar M m).property
  have hUQ := openCubeSet_subset_of_mem_descendantsAtDepth hU
  have hEllQ := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
    M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos hσ (oldCutoffSkewCoefficient m Q ω)
  have hEllU := hEllQ.mono (measurableSet_openCubeSet U) hUQ
  have hEllC := responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet U)
    M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos hσ
    (oldSignedCellCoefficient Q U hUQ (oldCutoffSkewCoefficient m Q ω))
  refine hist_congr_ae U _ _ _ hEllU hEllC ?_
  filter_upwards [ae_restrict_mem (measurableSet_openCubeSet U)] with x hx
  simp only [responseFramePlanarCoefficientField]
  rw [old_signed_cell_coefficient_extension_eq Q U (openCubeSet_subset_of_mem_descendantsAtDepth hU) _ hx]

section Pathwise

variable (M : ABKModel 2) (h : ℝ) (m : ℤ) {a b c d : ℝ} (hab : a < b) (hcd : c < d)
  (hQ : openCubeSet (originCube 2 (m + 129)) ⊆ openRectangle a b c d) (e : Vec 2)

/-- The pathwise inner budget of the final configuration. -/
theorem inner_pathwise (ell : ℤ)
    (hK : closedRectangle a b c d ⊆ openCubeSet (originCube 2 ell)) (ω : Cutoff.CutoffSample 2)
    (n : ℕ) :
    (finalCfg M h m hab hcd hQ e).innerLam n (olderField (closedRectangle a b c d) m ω) ≤
      ((44 / 25 : ℝ) * bhist M m (originCube 2 (m + 129)) 134 ω) ^ 2 *
        (defectA ^ 2 * (finalCfg M h m hab hcd hQ e).amp ^ 2) *
        dirTiledBot M m (originCube 2 (m + 129)) e ω := by
  let C := finalCfg M h m hab hcd hQ e
  let old := olderField (closedRectangle a b c d) m ω
  have hrest : C.Rest old = oldCutoffSkewCoefficient m C.Q ω :=
    rest_old_eq M (closedRectangle a b c d) ell m hK C.Q C.hQcl ω
  have hB : ∀ U ∈ descendantsAtDepth C.Q 134, lemmaVInverseHistory U
      (responseFramePlanarCoefficientField C.ν C.σ (C.Rest old)) ((3 : ℝ) ^ (1 / 4 : ℝ)) ≤
        bhist M m C.Q 134 ω := by
    intro U hU
    rw [hrest]
    exact hist_le_Bhist M m C.Q U hU ω
  have hin := C.inner_weak_sum (mesh' m) old n (Bhist_nonneg M m C.Q 134 ω) hB
  have hflat := final_flat_budget M h m hab hcd hQ e ell hK ω
  have hc : (1 + (3 : ℝ) ^ (-(1 / 4 : ℝ))) ≤ 44 / 25 := by
    have := three_pow_neg_quarter_le
    linarith
  have hB0 := Bhist_nonneg M m C.Q 134 ω
  have hsq : ((1 + (3 : ℝ) ^ (-(1 / 4 : ℝ))) * bhist M m C.Q 134 ω) ^ 2 ≤
      ((44 / 25 : ℝ) * bhist M m C.Q 134 ω) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg (by positivity) hB0) (mul_le_mul_of_nonneg_right hc hB0) 2
  have hT0 : 0 ≤ dirTiledBot M m C.Q e ω := by
    rw [← hflat]
    exact add_nonneg (lemmaVTiledWeakEnergy_nonneg _ _ _) (lemmaVTiledWeakEnergy_nonneg _ _ _)
  have hA0 : 0 ≤ defectA ^ 2 * C.amp ^ 2 := by positivity
  change C.innerLam n old ≤ _
  unfold Cfg''.innerLam
  refine hin.trans ?_
  rw [hflat]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsq hA0) hT0

end Pathwise

end

end ASDExplicitGamma.Scalar
