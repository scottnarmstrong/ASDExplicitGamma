module

public import ASDExplicitGamma.Scalar.UpperCellEnergyResetMatrix
public import ASDExplicitGamma.Scalar.UpperCellEnergyFutureProfile
public import ASDExplicitGamma.Scalar.FullResponseHistory

/-! Physical full-operator history for the UPPER RESET residual. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Algsuperdiff.Section3 Native Inverse
open scoped ENNReal
noncomputable section

private theorem reset_finite_max_ofReal {ι Ω : Type*} (s : Finset ι)
    (hs : s.Nonempty) (f : ι → Ω → ℝ) (ω : Ω) :
    historyFiniteMax s (fun i ω => ENNReal.ofReal (f i ω)) ω =
      ENNReal.ofReal (Book.Ch02.finsetSupReal s (fun i => f i ω)) := by
  classical
  have hf := s.finite_toSet.image (fun i => f i ω)
  have hn := hs.to_set.image (fun i => f i ω)
  obtain ⟨i, hi, heq⟩ := hn.csSup_mem hf
  apply le_antisymm
  · apply Finset.sup_le
    intro i hi
    exact ENNReal.ofReal_le_ofReal (le_csSup hf.bddAbove ⟨i,hi,rfl⟩)
  · change ENNReal.ofReal (sSup ((fun i => f i ω) '' (s : Set ι))) ≤ _
    rw [←heq]
    exact Finset.le_sup (f := fun i => ENNReal.ofReal (f i ω)) hi

/-- Every physical depth maximum is bounded by the actual full-trace maximum,
without replacing the physical coefficient or its OLD normalization. -/
theorem upper_cell_reset_depth_le_trace
    (M : ABKModel 2) (n : ℤ) (height j : ℕ) (weights : ℤ → ℝ)
    (ω : Cutoff.CutoffSample 2) :
    ENNReal.ofReal (fullResponseDepthMax (originCube 2 (n-14))
      ((Annealed.sigmaBar M n:ℝ)⁻¹ •
        attenuatedCoefficient M n (n+(height:ℤ)) weights ω) j) ≤
      upperCellFutureDepthMax M n height j weights ω := by
  rw [upperCellFutureDepthMax,
    reset_finite_max_ofReal _ (descendantsAtDepth_nonempty _ _)]
  apply ENNReal.ofReal_le_ofReal
  exact Book.Ch02.finsetSupReal_mono _ (descendantsAtDepth_nonempty _ _)
    (fun Q _ => upper_cell_reset_normalized_operator_le_full_trace M n _ weights Q ω)

/-- The complete physical full-response history is dominated by the
complete trace history, with the exact quarter-power discount. -/
theorem upper_cell_future_physical_history_le_trace
    (M : ABKModel 2) (n : ℤ) (height : ℕ) (weights : ℤ → ℝ)
    (ω : Cutoff.CutoffSample 2) :
    completeFullResponseHistory (originCube 2 (n-14))
      ((Annealed.sigmaBar M n:ℝ)⁻¹ •
        attenuatedCoefficient M n (n+(height:ℤ)) weights ω) ≤
      upperCellFutureHistory M n height weights ω := by
  have ha := inverse_history_discount_range
  unfold completeFullResponseHistory upperCellFutureHistory
  rw [←ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro j
  rw [ENNReal.ofReal_mul (pow_nonneg ha.1.le _)]
  have hw : ENNReal.ofReal (upperCellHistoryWeight j) =
      ENNReal.ofReal (1-inverseHistoryDiscount)*ENNReal.ofReal (inverseHistoryDiscount^j) := by
    rw [←ENNReal.ofReal_mul (sub_nonneg.mpr ha.2.le)]
    rfl
  rw [hw, mul_assoc]
  exact mul_le_mul' le_rfl (mul_le_mul' le_rfl
    (upper_cell_reset_depth_le_trace M n height j weights ω))

/-- The physical complete history is a measurable extended nonnegative
random variable before any finiteness or real interpretation is used. -/
theorem upper_cell_future_physical_history_measurable
    (M : ABKModel 2) (n : ℤ) (height : ℕ) (weights : ℤ → ℝ) :
    Measurable (fun ω : Cutoff.CutoffSample 2 =>
      completeFullResponseHistory (originCube 2 (n-14))
        ((Annealed.sigmaBar M n:ℝ)⁻¹ •
          attenuatedCoefficient M n (n+(height:ℤ)) weights ω)) := by
  have hd (j : ℕ) : Measurable (fun ω : Cutoff.CutoffSample 2 =>
      fullResponseDepthMax (originCube 2 (n-14))
        ((Annealed.sigmaBar M n:ℝ)⁻¹ •
          attenuatedCoefficient M n (n+(height:ℤ)) weights ω) j) := by
    let f := fun Q ω => fullResponseOperatorNorm Q
      ((Annealed.sigmaBar M n:ℝ)⁻¹ •
        attenuatedCoefficient M n (n+(height:ℤ)) weights ω)
    have hm := history_finite_max_measurable
      (descendantsAtDepth (originCube 2 (n-14)) j)
      (fun Q ω => ENNReal.ofReal (f Q ω))
      (fun Q => (upper_cell_reset_normalized_operator_measurable M n _ weights Q).ennreal_ofReal)
    have heq : (fun ω => fullResponseDepthMax (originCube 2 (n-14))
        ((Annealed.sigmaBar M n:ℝ)⁻¹ •
          attenuatedCoefficient M n (n+(height:ℤ)) weights ω) j) =
        (fun ω => (historyFiniteMax (descendantsAtDepth (originCube 2 (n-14)) j)
          (fun Q ω => ENNReal.ofReal (f Q ω)) ω).toReal) := by
      funext ω
      rw [reset_finite_max_ofReal _ (descendantsAtDepth_nonempty _ _)]
      exact (ENNReal.toReal_ofReal (full_response_depth_max_nonneg _ _ _)).symm
    rw [heq]
    exact hm.ennreal_toReal
  exact measurable_const.mul (Measurable.tsum
    (fun j => ((hd j).const_mul _).ennreal_ofReal))

/-- The actual physical operator history has the full order-64 profile
budget and is finite almost surely. No history estimate is a premise. -/
theorem upper_cell_future_physical_history_L64
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ)
    (hpast : ∀ k < n, nativeInductionState M h k)
    (height : ℕ) (hb : M.gamma*(height:ℝ) ≤ 17/50) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc n (n+(height:ℤ)), 0 ≤ weights k ∧ weights k ≤ 1) :
    let H := fun ω : Cutoff.CutoffSample 2 =>
      completeFullResponseHistory (originCube 2 (n-14))
        ((Annealed.sigmaBar M n:ℝ)⁻¹ •
          attenuatedCoefficient M n (n+(height:ℤ)) weights ω)
    eLpNorm (fun ω => (H ω).toReal) 64 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (upperCellHistoryProfile M.gamma (M.gamma*(height:ℝ))) ∧
      (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure, H ω < ⊤) := by
  dsimp only
  have ht := upper_cell_future_history_profile M h hM hg n hpast height hb weights hw
  have hle := upper_cell_future_physical_history_le_trace M n height weights
  have hfinite := ht.2.mono (fun ω hω => lt_of_le_of_lt (hle ω) hω)
  refine ⟨le_trans ?_ ht.1, hfinite⟩
  apply eLpNorm_mono_ae_real
    (upper_cell_future_physical_history_measurable M n height weights).ennreal_toReal.aestronglyMeasurable
  filter_upwards [ht.2] with ω hω
  rw [Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg]
  exact ENNReal.toReal_mono hω.ne (hle ω)

end
end ASDExplicitGamma.Scalar
