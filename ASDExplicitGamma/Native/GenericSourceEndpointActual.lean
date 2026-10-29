module

public import ASDExplicitGamma.Native.GenericSourceWeakActual

/-! The actual generic source producer on the entire smaller-gamma ray. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- Actual complete generic weak source rows have the degree-one endpoint
majorant, without scaling any upward-rounded operation at smaller gamma. -/
theorem native_source_generic_weak_actual_endpoint
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ k < m, nativeInductionState M h k) (r : ℕ) (hr : r ≤ 5) :
    nativeCompletedSourceWeak M m r ≤ ENNReal.ofReal (theta M*nativeSourceWeakInverseCharge
      (nativeSourceGenericCompleteMeanRow (17/50000) 1 r 1285)
      (nativeSourceGenericCompleteWeakRow (17/50000) 1 r 1285)) := by
  have hg0 := M.shellPrefix.gamma_pos.le
  have hW := native_source_generic_complete_mean_row_degree M.gamma (theta M) r 1285 hg0 hg rfl hr (by norm_num)
  have hV := native_source_generic_complete_weak_row_degree M.gamma (theta M) r 1285 hg0 hg rfl hr (by norm_num)
  exact (native_source_generic_weak_actual M h hM hg m hpast r hr).trans (ENNReal.ofReal_le_ofReal
    (native_source_weak_inverse_charge_degree (theta M) _ _ _ _ hW hV))

/-- The actual finite generic mean has the source's degree-one endpoint
majorant at each completed source depth. -/
theorem native_source_depth_generic_mean_endpoint
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ k < m, nativeInductionState M h k) (depth : ℕ) (hdepth : 9+depth ≤ 1332) :
    nativeCompletedSourceMean M m depth ≤
      ENNReal.ofReal (theta M*nativeSourceGenericMeanProfile (17/50000) 1 (9+depth)) := by
  have hdegree := native_source_generic_mean_profile_degree M.gamma (theta M) (9+depth)
    M.shellPrefix.gamma_pos.le hg rfl hdepth
  exact (native_source_depth_generic_mean_ennreal M h hM hg m hpast depth hdepth).trans
    (ENNReal.ofReal_le_ofReal hdegree)

end
end ASDExplicitGamma.Native
