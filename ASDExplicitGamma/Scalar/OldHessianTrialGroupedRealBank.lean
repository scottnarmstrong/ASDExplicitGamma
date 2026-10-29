module

public import ASDExplicitGamma.Scalar.OldHessianTrialGroupedBank

/-! Real random variables for the actual finite grouped history and rare
part. Finiteness is proved before either real conversion is used. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Inverse Algsuperdiff.Section3
open scoped ENNReal
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- The actual large-parent history bank, after its a.e. finiteness proof. -/
def oldHessianGroupedBank (M : ABKModel 2) (m : ℤ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  (inverseBankGroupedHistory (oldHessianMacroCells m) (fun Q => bankObserverRootUnion Q 5)
    M m (m+40) (bankPartialInsertionWeights m 1 0) ω).toReal

/-- The actual grouped rare part, with the scalar reserve 5*10^-24. -/
def oldHessianGroupedRare (M : ABKModel 2) (m : ℤ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  (inverseBankGroupedRemainder .globalInverse (oldHessianMacroCells m)
    (fun Q => bankObserverRootUnion Q 5) M m (m+40) (bankPartialInsertionWeights m 1 0) ω).toReal

/-- A finite extended bank and its real representative have identical
Lp norms; the finiteness premise is never discarded via toReal. -/
theorem old_hessian_finite_bank_norm {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : Ω → ℝ≥0∞) (p : ℝ≥0∞)
    (hY : ∀ᵐ ω ∂μ,Y ω<⊤) :
    eLpNorm Y p μ=eLpNorm (fun ω => (Y ω).toReal) p μ := by
  calc
    _ = eLpNorm (fun ω => ENNReal.ofReal (Y ω).toReal) p μ :=
      (eLpNorm_congr_ae (ofReal_toReal_ae_eq hY)).symm
    _ = _ := eLpNorm_ofReal _ (Filter.Eventually.of_forall fun _ => ENNReal.toReal_nonneg)

/-- Actual measurability, total and rare L128 bounds and the real positive
split, all discharged from the proved grouped bank. -/
theorem old_hessian_actual_grouped_real_bank
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (N : ℤ)
    (hpast : ∀ k<N,nativeInductionState M h k) (m : ℤ) (hm : m<N) :
    Measurable (oldHessianGroupedBank M m) ∧
    Measurable (oldHessianGroupedRare M m) ∧
    eLpNorm (oldHessianGroupedBank M m) 128 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (14103/10000:ℝ) ∧
    eLpNorm (oldHessianGroupedRare M m) 128 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (5/10^24:ℝ) ∧
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      oldHessianGroupedBank M m ω≤(14103/10000:ℝ)+oldHessianGroupedRare M m ω := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let Y := inverseBankGroupedHistory (oldHessianMacroCells m) (fun Q => bankObserverRootUnion Q 5)
    M m (m+40) (bankPartialInsertionWeights m 1 0)
  let R := inverseBankGroupedRemainder .globalInverse (oldHessianMacroCells m)
    (fun Q => bankObserverRootUnion Q 5) M m (m+40) (bankPartialInsertionWeights m 1 0)
  have hY : Measurable Y := history_finite_max_measurable _ _ (fun Q =>
    history_finite_max_measurable _ _ (fun U =>
      bank_root_inverse_history_measurable U.val M m (m+40) (bankPartialInsertionWeights m 1 0)))
  have hR : Measurable R := history_finite_max_measurable _ _ (fun Q =>
    ENNReal.continuous_ofReal.measurable.comp
      (inverse_bank_population_remainder_measurable .globalInverse (bankObserverRootUnion Q 5)
        M m (m+40) (bankPartialInsertionWeights m 1 0)))
  have hsplit := old_hessian_parent_grouped_split M h hM hg N hpast m hm
  have hbank := old_hessian_parent_grouped_bank M h hM hg N hpast m hm
  have hYf : ∀ᵐ ω ∂μ,Y ω<⊤ := hsplit.mono (fun _ hω => hω.1)
  have hRf : ∀ᵐ ω ∂μ,R ω<⊤ := hsplit.mono (fun _ hω => hω.2.1)
  refine ⟨ENNReal.measurable_toReal.comp hY,ENNReal.measurable_toReal.comp hR,?_,?_,?_⟩
  · change eLpNorm (fun ω => (Y ω).toReal) 128 μ ≤ _
    rw [←old_hessian_finite_bank_norm μ Y 128 hYf]
    exact hbank.2.2
  · change eLpNorm (fun ω => (R ω).toReal) 128 μ ≤ _
    rw [←old_hessian_finite_bank_norm μ R 128 hRf]
    exact hbank.2.1
  · filter_upwards [hsplit] with ω hω
    have ht := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,hω.2.1.ne⟩) hω.2.2
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top hω.2.1.ne,ENNReal.toReal_ofReal (by norm_num)] at ht
    exact ht

end
end ASDExplicitGamma.Scalar
