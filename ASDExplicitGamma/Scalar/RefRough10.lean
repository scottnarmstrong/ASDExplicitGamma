module

public import ASDExplicitGamma.Scalar.RefRough9
public import ASDExplicitGamma.Scalar.T4v2Final

/-! The `L^{128/127}` rough bound `‖Λ‖ ≤ amp² R` with the explicit constant `R = roughR`, and
integrability of the forced functional `F_w`, derived from the pathwise rough bounds
(no `L^{128/127}` cap on `F_w` is used). -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
  ASDExplicitGamma.Native
open Algsuperdiff.Section3
open scoped BigOperators ENNReal

attribute [local irreducible] Homogenization.descendantsAtDepth

noncomputable section

section Rough

variable (M : ABKModel 2) (h : ℝ) (m : ℤ) {a b c d : ℝ} (hab : a < b) (hcd : c < d)
  (hQ : openCubeSet (originCube 2 (m + 129)) ⊆ openRectangle a b c d) (e : Vec 2)

local notation "CC" => finalCfg M h m hab hcd hQ e

/-- The measurable majorant `((44/25) B* + 1)⁴` lies in `L^{128/127}`. -/
theorem majorant_memLp (hM : PlanarQ3Gaussian M h) (hγ : M.gamma ≤ gammaZero)
    (hpast : ∀ n ≤ m, nativeInductionState M h n) :
    eLpNorm (fun ω => ((44 / 25 : ℝ) * bhist M m (originCube 2 (m + 129)) 134 ω + 1) ^ 4)
        (ENNReal.ofReal (128 / 127)) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (((44 / 25 : ℝ) * (14103 / 10000) + 1) ^ 4) := by
  haveI : IsProbabilityMeasure (Cutoff.cutoffSampleLaw M).toMeasure := inferInstance
  have hQs : (originCube 2 (m + 129)).scale = m + 129 := by simp [originCube]
  have hbank := (bank_B M h hM hγ m (fun n hn => hpast n hn.le) (originCube 2 (m + 129)) hQs).1
  exact eLpNorm_pow4 (Cutoff.cutoffSampleLaw M).toMeasure _
    (Bhist_measurable M m _) (fun ω => Bhist_nonneg M m _ 134 ω) _ _ (by norm_num)
    (by norm_num) hbank

include h hab hcd hQ

/-- Pathwise rough bound for the forced part. -/
theorem forced_rough_pathwise (ell : ℤ)
    (hK : closedRectangle a b c d ⊆ openCubeSet (originCube 2 ell)) (ω : Cutoff.CutoffSample 2)
    (he2 : vecNormSq e = 1) (n : ℕ) :
    (CC).forcedLamR n (olderField (closedRectangle a b c d) m ω) ≤
    (CC).amp ^ 2 * (defectA ^ 2 *
      ((44 / 25 : ℝ) * bhist M m (originCube 2 (m + 129)) 134 ω + 1) ^ 4) := by
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
  have hB0 := Bhist_nonneg M m C.Q 134 ω
  have hf := C.forced_rough hQ (mesh' m) he2 old n hB0 hB
  have hF0 : 0 ≤ C.forcedLamR n old := by
    unfold Cfg''.forcedLamR
    exact add_nonneg (Finset.sum_nonneg fun j _ => lemmaVTiledWeakEnergy_nonneg _ _ _)
      (Finset.sum_nonneg fun j _ => lemmaVTiledWeakEnergy_nonneg _ _ _)
  have hA0 : 0 ≤ defectA := by unfold defectA; positivity
  have hg1 : 1 ≤ (44 / 25 : ℝ) * bhist M m C.Q 134 ω + 1 := by linarith
  have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) hf 2
  rw [Real.sq_sqrt hF0] at hsq
  refine hsq.trans ?_
  have h42 : ((44 / 25 : ℝ) * bhist M m C.Q 134 ω + 1) ^ 2 ≤
      ((44 / 25 : ℝ) * bhist M m C.Q 134 ω + 1) ^ 4 :=
    pow_le_pow_right₀ hg1 (by norm_num)
  have hpos : 0 ≤ C.amp ^ 2 * defectA ^ 2 := by positivity
  calc (defectA * |C.amp| * ((44 / 25 : ℝ) * bhist M m C.Q 134 ω + 1)) ^ 2
      = (C.amp ^ 2 * defectA ^ 2) * ((44 / 25 : ℝ) * bhist M m C.Q 134 ω + 1) ^ 2 := by
        simp only [mul_pow, sq_abs]; ring
    _ ≤ (C.amp ^ 2 * defectA ^ 2) * ((44 / 25 : ℝ) * bhist M m C.Q 134 ω + 1) ^ 4 :=
        mul_le_mul_of_nonneg_left h42 hpos
    _ = C.amp ^ 2 * (defectA ^ 2 *
        ((44 / 25 : ℝ) * bhist M m C.Q 134 ω + 1) ^ 4) := by ring

/-- **hΛq at the explicit constant**: `‖Λ_n‖_{L^{128/127}} ≤ amp² R`. -/
theorem budget_LamQ_rough (hM : PlanarQ3Gaussian M h) (hγ : M.gamma ≤ gammaZero)
    (hpast : ∀ n ≤ m, nativeInductionState M h n) (he2 : vecNormSq e = 1) (ell : ℤ)
    (hK : closedRectangle a b c d ⊆ openCubeSet (originCube 2 ell)) (n : ℕ) :
    eLpNorm (fun ω => (CC).LamFR n (olderField (closedRectangle a b c d) m ω) +
        (CC).LamGR n (olderField (closedRectangle a b c d) m ω))
        (ENNReal.ofReal (128 / 127)) (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal ((CC).amp ^ 2 * roughR) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  haveI : IsProbabilityMeasure μ := inferInstance
  have hmeasOld : Measurable (fun ω : Cutoff.CutoffSample 2 =>
      olderField (closedRectangle a b c d) m ω) := measurable_olderField _ ell m hK
  have hΛm : Measurable (fun ω : Cutoff.CutoffSample 2 =>
      (CC).LamFR n (olderField (closedRectangle a b c d) m ω) +
      (CC).LamGR n (olderField (closedRectangle a b c d) m ω)) :=
    (((CC).LamFR_measurable n).comp hmeasOld).add (((CC).LamGR_measurable n).comp hmeasOld)
  set H : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    ((44 / 25 : ℝ) * bhist M m (originCube 2 (m + 129)) 134 ω + 1) ^ 4 with hH
  have hH0 : ∀ ω, 0 ≤ H ω := fun ω => by
    have := Bhist_nonneg M m (originCube 2 (m + 129)) 134 ω
    simp only [hH]; positivity
  have hA0 : 0 ≤ (CC).amp ^ 2 * defectA ^ 2 := by unfold defectA; positivity
  have hmono : eLpNorm (fun ω => (CC).LamFR n (olderField (closedRectangle a b c d) m ω) +
        (CC).LamGR n (olderField (closedRectangle a b c d) m ω)) (ENNReal.ofReal (128 / 127)) μ ≤
      eLpNorm (((CC).amp ^ 2 * defectA ^ 2) • H) (ENNReal.ofReal (128 / 127)) μ := by
    refine eLpNorm_mono hΛm.aestronglyMeasurable (fun ω => ?_)
    have hΛ0 := add_nonneg ((CC).LamFR_nonneg n (olderField (closedRectangle a b c d) m ω))
      ((CC).LamGR_nonneg n (olderField (closedRectangle a b c d) m ω))
    have hp := Lam_rough_pathwise M h m hab hcd hQ e he2 ell hK ω n
    have hR0 : 0 ≤ ((CC).amp ^ 2 * defectA ^ 2) * H ω := mul_nonneg hA0 (hH0 ω)
    rw [Real.norm_eq_abs, abs_of_nonneg hΛ0]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Real.norm_eq_abs, abs_of_nonneg hR0]
    refine hp.trans (le_of_eq ?_)
    simp only [hH]; ring
  have hpow := majorant_memLp M h m hM hγ hpast
  refine hmono.trans ?_
  rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hA0]
  calc ENNReal.ofReal ((CC).amp ^ 2 * defectA ^ 2) *
        eLpNorm H (ENNReal.ofReal (128 / 127)) μ
      ≤ ENNReal.ofReal ((CC).amp ^ 2 * defectA ^ 2) *
        ENNReal.ofReal (((44 / 25 : ℝ) * (14103 / 10000) + 1) ^ 4) := by gcongr
    _ = _ := by
      rw [← ENNReal.ofReal_mul hA0]
      congr 1
      unfold roughR; ring

/-- The forced functional `F_w` (over the modes `t4v2S n`) is integrable. -/
theorem Fw_integrable (hM : PlanarQ3Gaussian M h) (hγ : M.gamma ≤ gammaZero)
    (hpast : ∀ n ≤ m, nativeInductionState M h n) (he2 : vecNormSq e = 1) (ell : ℤ)
    (hK : closedRectangle a b c d ⊆ openCubeSet (originCube 2 ell)) (n : ℕ) :
    Integrable (fun ω => fwStar (t4v2S n) M m (originCube 2 (m + 1 + 128)) 134
      (lambda8Q3ParentModePotential M h e (m + 1))
      (oldMaxFam M m (originCube 2 (m + 1 + 128))
        (lambda8Q3ParentModePotential M h e (m + 1))) ω) (Cutoff.cutoffSampleLaw M).toMeasure := by
  classical
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  haveI : IsProbabilityMeasure μ := inferInstance
  let Qb := originCube 2 (m + 1 + 128)
  let Fw : Cutoff.CutoffSample 2 → ℝ := fun ω => fwStar (t4v2S n) M m Qb 134
    (lambda8Q3ParentModePotential M h e (m + 1))
    (oldMaxFam M m Qb (lambda8Q3ParentModePotential M h e (m + 1))) ω
  have hFm : Measurable Fw := by
    rcases (t4v2S n).eq_empty_or_nonempty with h0 | ⟨i, hi⟩
    · have : Fw = fun _ => 0 := by
        funext ω; simp [Fw, fwStar, h0]
      rw [this]; exact measurable_const
    · exact (oldMaxFam_measurable (t4v2S n) M m Qb 134
        (lambda8Q3ParentModePotential M h e (m + 1)) i).2
  have hσ2 : 0 < (CC).σ ^ 2 := by have := (CC).hσ; positivity
  set H : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    ((44 / 25 : ℝ) * bhist M m (originCube 2 (m + 129)) 134 ω + 1) ^ 4 with hH
  have hHm : Measurable H := by
    simp only [hH]
    exact (((Bhist_measurable M m _).const_mul _).add_const 1).pow_const 4
  have hHmem : MemLp H (ENNReal.ofReal (128 / 127)) μ := by
    exact lt_of_le_of_lt (majorant_memLp M h m hM hγ hpast) ENNReal.ofReal_lt_top
  have hmem : MemLp Fw (ENNReal.ofReal (128 / 127)) μ := by
    refine (hHmem.const_mul ((CC).σ ^ 2 * ((CC).amp ^ 2 * defectA ^ 2))).mono'
      hFm.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    have heq := T4v2_pathwise M h m hab hcd hQ e n
      (ω := ω)
    have hF0 : 0 ≤ (CC).forcedLamR n (olderField (closedRectangle a b c d) m ω) := by
      unfold Cfg''.forcedLamR
      exact add_nonneg (Finset.sum_nonneg fun j _ => lemmaVTiledWeakEnergy_nonneg _ _ _)
        (Finset.sum_nonneg fun j _ => lemmaVTiledWeakEnergy_nonneg _ _ _)
    have hFe : Fw ω = (CC).σ ^ 2 * (CC).forcedLamR n (olderField (closedRectangle a b c d) m ω) := by
      rw [heq]; show _ = _ * (((CC).σ ^ 2)⁻¹ * Fw ω)
      exact (mul_inv_cancel_left₀ hσ2.ne' _).symm
    have hp := forced_rough_pathwise M h m hab hcd hQ e ell hK ω he2 n
    have hFn : 0 ≤ Fw ω := by rw [hFe]; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hFn, hFe]
    calc (CC).σ ^ 2 * (CC).forcedLamR n (olderField (closedRectangle a b c d) m ω)
        ≤ (CC).σ ^ 2 * ((CC).amp ^ 2 * (defectA ^ 2 * H ω)) :=
          mul_le_mul_of_nonneg_left hp hσ2.le
      _ = _ := by ring
  refine hmem.integrable ?_
  rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

end Rough

end

end ASDExplicitGamma.Scalar
