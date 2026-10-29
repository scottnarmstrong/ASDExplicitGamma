module

public import ASDExplicitGamma.Inverse.BankInverseProfiles
public import ASDExplicitGamma.Inverse.PointwiseRoot
public import ASDExplicitGamma.Inverse.RootMeanInputs

/-! Actual finite populations of complete inverse histories in one true frame. -/
@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Numerics.Inverse
open scoped ENNReal

/-- The source positive truncation of the actual observer population. -/
noncomputable def inverseBankPopulationRemainder (r : InverseBankRow)
    (s : Finset (TriadicCube 2)) (M : ABKModel 2) (m J : ℤ) (weights : ℤ → ℝ)
    (ω : Cutoff.CutoffSample 2) : ℝ :=
  positiveSplitRemainder (bankFiniteRootHistoryMax s M m J weights ω).toReal
    (inverseBankA r:ℝ) (1/2000)

theorem inverse_bank_population_remainder_measurable (r : InverseBankRow)
    (s : Finset (TriadicCube 2)) (M : ABKModel 2) (m J : ℤ) (weights : ℤ → ℝ) :
    Measurable (inverseBankPopulationRemainder r s M m J weights) := by
  have hY : Measurable (bankFiniteRootHistoryMax s M m J weights) :=
    history_finite_max_measurable _ _ (fun Q =>
      bank_root_inverse_history_measurable Q.1 M m J weights)
  exact measurable_const.max
    (((ENNReal.measurable_toReal.comp hY).sub_const (inverseBankA r:ℝ)).sub_const (1/2000))

/-- The literal complete histories have the source A/e pretruncation split.
The baseline pays the six-generation frame cost once; only the remainder
pays the population, including the union of all six source refinements. -/
theorem inverse_bank_population_pretruncation
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (r : InverseBankRow)
    (s : Finset (TriadicCube 2)) (m J : ℤ) (hmJ : m ≤ J)
    (weights : ℤ → ℝ) (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1)
    (hscale : ∀ Q ∈ s, Q.scale ≤ m ∧ m-Q.scale ≤ 5) (hcard : s.card ≤ 6*9^45)
    (hpast : ∀ n < m, nativeInductionState M h n)
    (hmean : ClippedInverseMeanInput M m (inverseBankRootRow r)) :
    Measurable (bankFiniteRootHistoryMax s M m J weights) ∧
      Measurable (bankFiniteRootRemainderHistoryMax s M m (inverseBankRootRow r)) ∧
      (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
        bankFiniteRootHistoryMax s M m J weights ω ≤ ENNReal.ofReal (inverseBankA r:ℝ) +
          bankFiniteRootRemainderHistoryMax s M m (inverseBankRootRow r) ω) ∧
      eLpNorm (bankFiniteRootRemainderHistoryMax s M m (inverseBankRootRow r)) 256
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal (inverseBankE r:ℝ) := by
  classical
  rcases inverse_bank_profile_nonneg r with ⟨hA0,hE0,hLi0,hRho0,hHeight0⟩
  have hf0 : 0 ≤ (invE (11/5*invGamma):ℝ) := by norm_num [invE,invGamma]
  have hg0 : 0 ≤ (invE (11*invGamma):ℝ) := by norm_num [invE,invGamma]
  have hp0 : 0 ≤ (invPopulationRoot:ℝ) := by norm_num [invPopulationRoot]
  have hb0 : 0 ≤ (invSB:ℝ) := by
    norm_num [invSB, invAlphaLower, invAlphaUpper, invE, invGamma]
  have hr0 : 0 ≤ (invSR:ℝ) := by
    norm_num [invSR, invAlphaLower, invBetaUpper, invE, invGamma]
  have hABudget : ENNReal.ofReal (invE (11/5*invGamma):ℝ) *
      ENNReal.ofReal (invE (11*invGamma):ℝ) * ENNReal.ofReal (inverseBankLi r:ℝ) *
      ENNReal.ofReal (invE (11/5*invGamma*inverseBankHeight r):ℝ) *
      ENNReal.ofReal (invSB:ℝ) = ENNReal.ofReal (inverseBankA r:ℝ) := by
    rw [(inverse_bank_source_formulas r).1]
    simp only [Rat.cast_mul]
    repeat rw [ENNReal.ofReal_mul (by positivity)]
  have hEBudget : ENNReal.ofReal (invE (11/5*invGamma):ℝ) *
      ENNReal.ofReal (509/500:ℝ) * ENNReal.ofReal (invE (11*invGamma):ℝ) *
      ENNReal.ofReal (invPopulationRoot:ℝ) * ENNReal.ofReal (inverseBankRho r:ℝ) *
      ENNReal.ofReal (invSR:ℝ) = ENNReal.ofReal (inverseBankE r:ℝ) := by
    rw [(inverse_bank_source_formulas r).2]
    simp only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat]
    repeat rw [ENNReal.ofReal_mul (by positivity)]
  have hBase (Q : ↥s) : bankRootInverseBaselineHistory Q.1 M m (inverseBankRootRow r) ≤
      ENNReal.ofReal (inverseBankA r:ℝ) := by
    exact (bank_offset_baseline_profile_cap M Q.1 Q.1.scale m (inverseBankRootRow r)
      (inverseBankLi r:ℝ) (invE (11/5*invGamma*inverseBankHeight r):ℝ)
      rfl (hscale Q.1 Q.2).1 (hscale Q.1 Q.2).2 hg (inverse_bank_Li_bound M hg r)
      (inverse_bank_height_bound M hg r)).trans_eq hABudget
  have hY : Measurable (bankFiniteRootHistoryMax s M m J weights) :=
    history_finite_max_measurable _ _ (fun Q =>
      bank_root_inverse_history_measurable Q.1 M m J weights)
  have hRroot (Q : ↥s) : Measurable
      (bankRootInverseRemainderHistory Q.1 M m (inverseBankRootRow r)) :=
    bank_root_inverse_remainder_history_measurable M h hM hg Q.1 m J
      (hscale Q.1 Q.2).1 hmJ weights hw (inverseBankRootRow r)
      hpast hmean (q3_pointwise_root M h hM hg)
  have hR : Measurable (bankFiniteRootRemainderHistoryMax s M m (inverseBankRootRow r)) :=
    history_finite_max_measurable _ _ hRroot
  let B := ENNReal.ofReal (invE (11/5*invGamma):ℝ) *
    ENNReal.ofReal (invE (11*invGamma):ℝ) * ENNReal.ofReal (inverseBankRho r:ℝ) *
      ENNReal.ofReal (invSR:ℝ)
  have hBudget (Q : ↥s) : eLpNorm
      (bankRootInverseRemainderHistory Q.1 M m (inverseBankRootRow r)) 256
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ B := by
    have hn := bank_root_inverse_remainder_history_L256_of_pointwise M h hM hg
      Q.1 m J (hscale Q.1 Q.2).1 hmJ weights hw (inverseBankRootRow r)
      hpast hmean (q3_pointwise_root M h hM hg)
    exact hn.trans (bank_offset_remainder_profile_cap M Q.1 Q.1.scale m
      (inverseBankRootRow r) (inverseBankRho r:ℝ) rfl (hscale Q.1 Q.2).1
      (hscale Q.1 Q.2).2 hg (inverse_bank_error_bound M hg r))
  have hSplit (Q : ↥s) : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      bankRootInverseHistory Q.1 M m J weights ω ≤ ENNReal.ofReal (inverseBankA r:ℝ) +
        bankRootInverseRemainderHistory Q.1 M m (inverseBankRootRow r) ω := by
    filter_upwards [bank_root_inverse_history_split_of_pointwise M h Q.1 m J
      (hscale Q.1 Q.2).1 hmJ weights hw (inverseBankRootRow r) hpast hmean
      (q3_pointwise_root M h hM hg)] with ω hω
    exact hω.trans (add_le_add (hBase Q) le_rfl)
  refine ⟨hY,hR,?_,?_⟩
  · filter_upwards [ae_all_iff.mpr hSplit] with ω hω
    change (Finset.univ : Finset ↥s).sup
      (fun Q => bankRootInverseHistory Q.1 M m J weights ω) ≤ _
    apply Finset.sup_le
    intro Q hQ
    exact (hω Q).trans (add_le_add le_rfl (Finset.le_sup
      (f := fun Q : ↥s => bankRootInverseRemainderHistory Q.1 M m (inverseBankRootRow r) ω) hQ))
  · have hRnorm := bank_finite_max_L256 (Cutoff.cutoffSampleLaw M).toMeasure
      (Finset.univ : Finset ↥s)
      (fun Q : ↥s => bankRootInverseRemainderHistory Q.1 M m (inverseBankRootRow r))
      hRroot B (fun Q _ => hBudget Q)
    have hRnorm' : eLpNorm
        (bankFiniteRootRemainderHistoryMax s M m (inverseBankRootRow r)) 256
          (Cutoff.cutoffSampleLaw M).toMeasure ≤ (s.card:ℝ≥0∞)^(1/256:ℝ)*B := by
      change eLpNorm (historyFiniteMax (Finset.univ : Finset ↥s)
        (fun Q : ↥s => bankRootInverseRemainderHistory Q.1 M m (inverseBankRootRow r))) 256
          (Cutoff.cutoffSampleLaw M).toMeasure ≤ _
      simpa only [Finset.card_univ, Fintype.card_coe] using hRnorm
    calc
      _ ≤ (s.card:ℝ≥0∞)^(1/256:ℝ) * B := hRnorm'
      _ ≤ (ENNReal.ofReal (509/500:ℝ)*ENNReal.ofReal (invPopulationRoot:ℝ)) *
          (ENNReal.ofReal (invE (11/5*invGamma):ℝ) *
            ENNReal.ofReal (invE (11*invGamma):ℝ) * ENNReal.ofReal (inverseBankRho r:ℝ) *
              ENNReal.ofReal (invSR:ℝ)) :=
        mul_le_mul_of_nonneg_right (bank_root_population_payment s.card hcard) bot_le
      _ = _ := by rw [← hEBudget]; ac_rfl

/-- Finite-family assembly after actual root baseline and remainder caps
have been supplied. This helper also applies to the depth-j source family. -/
theorem bank_finite_history_split_of_root_caps
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (r : RootRow)
    (s : Finset (TriadicCube 2)) (m J : ℤ) (hmJ : m ≤ J)
    (weights : ℤ → ℝ) (hw : ∀ k ∈ Finset.Ioc m J, 0 ≤ weights k ∧ weights k ≤ 1)
    (hscale : ∀ Q ∈ s, Q.scale ≤ m) (hpast : ∀ n < m, nativeInductionState M h n)
    (hmean : ClippedInverseMeanInput M m r) (A : ℝ) (E : ℝ≥0∞)
    (hBase : ∀ Q ∈ s, bankRootInverseBaselineHistory Q M m r ≤ ENNReal.ofReal A)
    (hCap : ∀ Q ∈ s, eLpNorm (bankRootInverseRemainderHistory Q M m r) 256
      (Cutoff.cutoffSampleLaw M).toMeasure ≤ E) :
    Measurable (bankFiniteRootHistoryMax s M m J weights) ∧
      Measurable (bankFiniteRootRemainderHistoryMax s M m r) ∧
      (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
        bankFiniteRootHistoryMax s M m J weights ω ≤ ENNReal.ofReal A +
          bankFiniteRootRemainderHistoryMax s M m r ω) ∧
      eLpNorm (bankFiniteRootRemainderHistoryMax s M m r) 256
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ (s.card:ℝ≥0∞)^(1/256:ℝ)*E := by
  classical
  have hY : Measurable (bankFiniteRootHistoryMax s M m J weights) :=
    history_finite_max_measurable _ _ (fun Q => bank_root_inverse_history_measurable Q.1 M m J weights)
  have hR (Q : ↥s) : Measurable (bankRootInverseRemainderHistory Q.1 M m r) :=
    bank_root_inverse_remainder_history_measurable M h hM hg Q.1 m J (hscale Q.1 Q.2)
      hmJ weights hw r hpast hmean (q3_pointwise_root M h hM hg)
  have hSplit (Q : ↥s) : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      bankRootInverseHistory Q.1 M m J weights ω ≤ ENNReal.ofReal A +
        bankRootInverseRemainderHistory Q.1 M m r ω := by
    filter_upwards [bank_root_inverse_history_split_of_pointwise M h Q.1 m J
      (hscale Q.1 Q.2) hmJ weights hw r hpast hmean (q3_pointwise_root M h hM hg)] with ω hω
    exact hω.trans (add_le_add (hBase Q.1 Q.2) le_rfl)
  refine ⟨hY,history_finite_max_measurable _ _ hR,?_,?_⟩
  · filter_upwards [ae_all_iff.mpr hSplit] with ω hω
    change (Finset.univ : Finset ↥s).sup (fun Q => bankRootInverseHistory Q.1 M m J weights ω) ≤ _
    apply Finset.sup_le
    intro Q hQ
    exact (hω Q).trans (add_le_add le_rfl (Finset.le_sup
      (f := fun Q : ↥s => bankRootInverseRemainderHistory Q.1 M m r ω) hQ))
  · have hh := bank_finite_max_L256 (Cutoff.cutoffSampleLaw M).toMeasure
      (Finset.univ : Finset ↥s) (fun Q : ↥s => bankRootInverseRemainderHistory Q.1 M m r)
      hR E (fun Q _ => hCap Q.1 Q.2)
    change eLpNorm (historyFiniteMax (Finset.univ : Finset ↥s)
      (fun Q : ↥s => bankRootInverseRemainderHistory Q.1 M m r)) 256
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ _
    simpa only [Finset.card_univ, Fintype.card_coe] using hh

end ASDExplicitGamma.Inverse
