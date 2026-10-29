module

public import ASDExplicitGamma.Native.OldSignedMeanSourceGenerator

/-! Actual one-shell OLD mean transport with the sharp source coefficient. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open MeasureTheory Set Homogenization Algsuperdiff.Section3 Inverse
noncomputable section

/-- The actual heat-panel slope is paid by the source generator coefficient. -/
theorem old_signed_actual_mean_source_slope
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ j < m, nativeInductionState M h j) (r : ℕ) :
    inSourceMeanSlopeActual M h m r ≤ oldSignedMeanSourceCap M h m r := by
  let S := inSourceMeanRateActual M h m r '' Set.Icc (0 : ℝ) 1
  have henergy := old_signed_actual_mean_source_generator M h hM hg m hpast r 0
    ⟨le_rfl, by norm_num⟩
  have hS_nonempty : S.Nonempty := by
    refine ⟨inSourceMeanRateActual M h m r 0, ?_⟩
    exact ⟨0, ⟨le_rfl, by norm_num⟩, rfl⟩
  have hsup : sSup S ≤ oldSignedMeanSourceCap M h m r := by
    apply csSup_le hS_nonempty
    rintro x ⟨t, ht, rfl⟩
    exact (old_signed_actual_mean_source_generator M h hM hg m hpast r t ht).1
  unfold inSourceMeanSlopeActual
  exact max_le henergy.2 hsup

/-- Actual partial mean transport. The OLD initial mean remains explicit;
no q1 or refined source-row estimate is used. -/
theorem old_signed_actual_mean_source_transport
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ)
    (hpast : ∀ l < n,nativeInductionState M h l) (r : ℕ)
    (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    inSourceMeanActual M n r t ≤ inSourceMeanActual M n r 0+
      t*oldSignedMeanSourceCap M h n r := by
  have hheat := in_source_actual_mean_transport_by_slope M h hM n r t ht
  have hslope := old_signed_actual_mean_source_slope M h hM hg n hpast r
  exact hheat.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hslope ht.1))

end
end ASDExplicitGamma.Native
