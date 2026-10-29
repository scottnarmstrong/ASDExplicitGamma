module

public import ASDExplicitGamma.Scalar.RefBudget3
public import ASDExplicitGamma.Scalar.RefRough10

/-! The hΛ1 budget of the corrected defect without any interface hypothesis: `T4 part 1` is `T4v2_pathwise`, and `F_w` integrability comes from the rough bound. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
  ASDExplicitGamma.Native
open Algsuperdiff.Section3
open scoped BigOperators ENNReal

attribute [local irreducible] Homogenization.descendantsAtDepth

noncomputable section

section Budget

variable (M : ABKModel 2) (h : ℝ) (m : ℤ) {a b c d : ℝ} (hab : a < b) (hcd : c < d)
  (hQ : openCubeSet (originCube 2 (m + 129)) ⊆ openRectangle a b c d) (e : Vec 2)

local notation "CC" => finalCfg M h m hab hcd hQ e

/-- **hΛ1 for the corrected defect**, conditional on the forced-part interface. -/
theorem budget_Lam1T (hM : PlanarQ3Gaussian M h) (hγ : M.gamma ≤ gammaZero)
    (hpast : ∀ n ≤ m, nativeInductionState M h n) (he : Book.Ch02.vecNorm e = 1)
    (he2 : vecNormSq e = 1) (ell : ℤ)
    (hK : closedRectangle a b c d ⊆ openCubeSet (originCube 2 ell))
    (n : ℕ) :
    ∫ ω, ((CC).LamFR n (olderField (closedRectangle a b c d) m ω) +
        (CC).LamGR n (olderField (closedRectangle a b c d) m ω))
        ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      (CC).amp ^ 2 * defectLambda mainSourceMeanPrefix (xi'' M h m) (mStar' M)
        (14103 / 10000) (5 / 10 ^ 24) := by
  classical
  let S : ℕ → Finset whiteBasisIndex := t4v2S
  have hS1 : ∀ n (ω : Cutoff.CutoffSample 2), (CC).forcedLamR n
      (olderField (closedRectangle a b c d) m ω) ≤ (((CC).σ ^ 2)⁻¹) *
      fwStar (S n) M m (originCube 2 (m + 1 + 128)) 134
        (lambda8Q3ParentModePotential M h e (m + 1))
        (oldMaxFam M m (originCube 2 (m + 1 + 128))
          (lambda8Q3ParentModePotential M h e (m + 1))) ω :=
    fun n ω => (T4v2_pathwise M h m hab hcd hQ e n ω).le
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  haveI : IsProbabilityMeasure μ := inferInstance
  let Qb := originCube 2 (m + 1 + 128)
  let Fw : Cutoff.CutoffSample 2 → ℝ := fun ω => fwStar (S n) M m Qb 134
    (lambda8Q3ParentModePotential M h e (m + 1))
    (oldMaxFam M m Qb (lambda8Q3ParentModePotential M h e (m + 1))) ω
  have hFm : Measurable Fw := by
    rcases (S n).eq_empty_or_nonempty with h0 | ⟨i, hi⟩
    · have : Fw = fun _ => 0 := by
        funext ω; simp [Fw, fwStar, h0]
      rw [this]; exact measurable_const
    · exact (oldMaxFam_measurable (S n) M m Qb 134 (lambda8Q3ParentModePotential M h e (m + 1)) i).2
  have hσ2 : 0 < ((CC).σ ^ 2)⁻¹ := by
    have := (CC).hσ
    positivity
  have hFw0 : ∀ ω, 0 ≤ Fw ω := by
    intro ω
    have h1 := hS1 n ω
    have h2 : 0 ≤ (CC).forcedLamR n (olderField (closedRectangle a b c d) m ω) := by
      unfold Cfg''.forcedLamR
      exact add_nonneg (Finset.sum_nonneg fun j _ => lemmaVTiledWeakEnergy_nonneg _ _ _)
        (Finset.sum_nonneg fun j _ => lemmaVTiledWeakEnergy_nonneg _ _ _)
    exact nonneg_of_mul_nonneg_right (h2.trans h1) hσ2
  have hFint : Integrable Fw μ := Fw_integrable M h m hab hcd hQ e hM hγ hpast he2 ell hK n
  obtain ⟨-, -, -, -, -, hFwI⟩ := sc_smooth_feedback_gap_modes (S n) M h hM hγ m hpast e he
  have hFwI' : ∫ ω, Fw ω ∂μ ≤ (h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * ((m + 1 : ℤ) : ℝ))) *
      consumerL mainSourceMeanPrefix (xi'' M h m) (1 / 2) lambda8DeltaN (mStar' M)
        (14103 / 10000) (5 / 10 ^ 24) (76 / 100) (76 / 100) ^ 2 := hFwI
  set L := consumerL mainSourceMeanPrefix (xi'' M h m) (1 / 2) lambda8DeltaN (mStar' M)
    (14103 / 10000) (5 / 10 ^ 24) (76 / 100) (76 / 100) with hLdef
  have hL0 : 0 ≤ L := by
    have hd : 0 ≤ lambda8DeltaN := by unfold lambda8DeltaN lambda8Rho; positivity
    rw [hLdef]; unfold consumerL; positivity
  set v : ℝ := h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * ((m + 1 : ℤ) : ℝ)) with hv
  have hamp := amp_sq M h m hab hcd hQ e
  -- the flux-affine series
  have hQs : (originCube 2 (m + 129)).scale = m + 129 := by simp [originCube]
  obtain ⟨hGint, hGle⟩ := dir_series_integral M h hM hγ m hpast (originCube 2 (m + 129)) hQs e he2
  let Ssum : Cutoff.CutoffSample 2 → ℝ := fun ω => ∑' j : ℕ,
    (1 - Scalar.inverseHistoryDiscount ^ 2) * Scalar.inverseHistoryDiscount ^ (2 * j) *
      depthMax M m (originCube 2 (m + 129)) ω (134 + j) *
        dirX M m (originCube 2 (m + 129)) e ω j
  let Bh : Cutoff.CutoffSample 2 → ℝ := fun ω => bhist M m (originCube 2 (m + 129)) 134 ω
  let G : Cutoff.CutoffSample 2 → ℝ := fun ω => Bh ω ^ 2 * Ssum ω
  have hα := Scalar.inverse_history_discount_range
  have hSsum0 : ∀ ω, 0 ≤ Ssum ω := fun ω => tsum_nonneg fun j => mul_nonneg (mul_nonneg
    (mul_nonneg (sub_nonneg.mpr (pow_le_one₀ hα.1.le hα.2.le)) (pow_nonneg hα.1.le _))
    (lemmaVInverseDepthMax_nonneg _ _ _)) (dirX_nonneg M m _ e ω j)
  have hG0 : ∀ ω, 0 ≤ G ω := fun ω => mul_nonneg (sq_nonneg _) (hSsum0 ω)
  have hξ : 0 ≤ xi'' M h m := by
    have h0 : 0 ≤ ∫ ω, G ω ∂μ := integral_nonneg hG0
    have := h0.trans hGle
    nlinarith [sq_nonneg (14103 / 10000 : ℝ)]
  set κ : ℝ := (44 / 25 : ℝ) * defectA * |(CC).amp| with hκ
  let X : Cutoff.CutoffSample 2 → ℝ := fun ω => Real.sqrt (((CC).σ ^ 2)⁻¹ * Fw ω)
  let Y : Cutoff.CutoffSample 2 → ℝ := fun ω => κ * Real.sqrt (G ω)
  have hX2e : ∀ ω, X ω ^ 2 = ((CC).σ ^ 2)⁻¹ * Fw ω := fun ω =>
    Real.sq_sqrt (mul_nonneg hσ2.le (hFw0 ω))
  have hY2e : ∀ ω, Y ω ^ 2 = κ ^ 2 * G ω := fun ω => by
    simp only [Y, mul_pow, Real.sq_sqrt (hG0 ω)]
  have hX2 : Integrable (fun ω => X ω ^ 2) μ := by
    simp_rw [hX2e]; exact hFint.const_mul _
  have hY2 : Integrable (fun ω => Y ω ^ 2) μ := by
    simp_rw [hY2e]; exact hGint.const_mul _
  have hXm : AEStronglyMeasurable X μ :=
    (Real.continuous_sqrt.comp_aestronglyMeasurable
      ((hFm.const_mul _).aestronglyMeasurable))
  have hYm : AEStronglyMeasurable Y μ :=
    (Real.continuous_sqrt.comp_aestronglyMeasurable hGint.aestronglyMeasurable).const_mul κ
  have hX0 : ∀ ω, 0 ≤ X ω := fun ω => Real.sqrt_nonneg _
  have hκ0 : 0 ≤ κ := by rw [hκ]; unfold defectA; positivity
  have hY0 : ∀ ω, 0 ≤ Y ω := fun ω => mul_nonneg hκ0 (Real.sqrt_nonneg _)
  -- pathwise
  have hpath : ∀ ω, (CC).LamFR n (olderField (closedRectangle a b c d) m ω) +
      (CC).LamGR n (olderField (closedRectangle a b c d) m ω) ≤ (X ω + Y ω) ^ 2 := by
    intro ω
    have hΛ0 := add_nonneg ((CC).LamFR_nonneg n (olderField (closedRectangle a b c d) m ω))
      ((CC).LamGR_nonneg n (olderField (closedRectangle a b c d) m ω))
    have h1 := (CC).lam_splitR n (olderField (closedRectangle a b c d) m ω)
    have h2 : Real.sqrt ((CC).forcedLamR n (olderField (closedRectangle a b c d) m ω)) ≤ X ω :=
      Real.sqrt_le_sqrt (hS1 n ω)
    have h3 : Real.sqrt ((CC).innerLam n (olderField (closedRectangle a b c d) m ω)) ≤ Y ω := by
      have hin := inner_pathwise M h m hab hcd hQ e ell hK ω n
      have hT := dirTiledBot_le_series M m (originCube 2 (m + 129)) e ω
      have hT0 : 0 ≤ dirTiledBot M m (originCube 2 (m + 129)) e ω := by
        exact le_of_le_of_eq (add_nonneg (lemmaVTiledWeakEnergy_nonneg _ _ _)
          (lemmaVTiledWeakEnergy_nonneg _ _ _)) (final_flat_budget M h m hab hcd hQ e ell hK ω)
      have hB0 := Bhist_nonneg M m (originCube 2 (m + 129)) 134 ω
      have hbound : (CC).innerLam n (olderField (closedRectangle a b c d) m ω) ≤ κ ^ 2 * G ω := by
        refine hin.trans ?_
        have hA : 0 ≤ ((44 / 25 : ℝ) * bhist M m (originCube 2 (m + 129)) 134 ω) ^ 2 *
            (defectA ^ 2 * (CC).amp ^ 2) := by positivity
        calc _ ≤ ((44 / 25 : ℝ) * bhist M m (originCube 2 (m + 129)) 134 ω) ^ 2 *
              (defectA ^ 2 * (CC).amp ^ 2) * Ssum ω := mul_le_mul_of_nonneg_left hT hA
          _ = κ ^ 2 * G ω := by
            rw [hκ]; simp only [G, Bh, mul_pow, sq_abs]; ring
      calc Real.sqrt ((CC).innerLam n (olderField (closedRectangle a b c d) m ω))
          ≤ Real.sqrt (κ ^ 2 * G ω) := Real.sqrt_le_sqrt hbound
        _ = Y ω := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hκ0]
    have h4 : Real.sqrt ((CC).LamFR n (olderField (closedRectangle a b c d) m ω) +
        (CC).LamGR n (olderField (closedRectangle a b c d) m ω)) ≤ X ω + Y ω :=
      h1.trans (add_le_add h2 h3)
    calc _ = Real.sqrt (_) ^ 2 := (Real.sq_sqrt hΛ0).symm
      _ ≤ (X ω + Y ω) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h4 2
  have hint := integral_sq_add_le μ X Y hXm hYm hX2 hY2
  have hΛle : ∫ ω, ((CC).LamFR n (olderField (closedRectangle a b c d) m ω) +
      (CC).LamGR n (olderField (closedRectangle a b c d) m ω)) ∂μ ≤ ∫ ω, (X ω + Y ω) ^ 2 ∂μ :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => add_nonneg
      ((CC).LamFR_nonneg n _) ((CC).LamGR_nonneg n _)) hint.1 (Filter.Eventually.of_forall hpath)
  have hXint : ∫ ω, X ω ^ 2 ∂μ ≤ (CC).amp ^ 2 * L ^ 2 := by
    have e1 : ∫ ω, X ω ^ 2 ∂μ = ((CC).σ ^ 2)⁻¹ * ∫ ω, Fw ω ∂μ := by
      simp_rw [hX2e]; exact integral_const_mul _ _
    rw [e1, hamp]
    calc ((CC).σ ^ 2)⁻¹ * ∫ ω, Fw ω ∂μ ≤ ((CC).σ ^ 2)⁻¹ * (v * L ^ 2) :=
          mul_le_mul_of_nonneg_left hFwI' hσ2.le
      _ = v * ((CC).σ ^ 2)⁻¹ * L ^ 2 := by ring
  have hYint : ∫ ω, Y ω ^ 2 ∂μ ≤ κ ^ 2 * ((14103 / 10000 : ℝ) ^ 2 * xi'' M h m / 2) := by
    have e1 : ∫ ω, Y ω ^ 2 ∂μ = κ ^ 2 * ∫ ω, G ω ∂μ := by
      simp_rw [hY2e]; exact integral_const_mul _ _
    rw [e1]
    exact mul_le_mul_of_nonneg_left hGle (sq_nonneg _)
  have hsX : Real.sqrt (∫ ω, X ω ^ 2 ∂μ) ≤ |(CC).amp| * L := by
    calc _ ≤ Real.sqrt ((CC).amp ^ 2 * L ^ 2) := Real.sqrt_le_sqrt hXint
      _ = |(CC).amp| * L := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, Real.sqrt_sq hL0]
  have hsY : Real.sqrt (∫ ω, Y ω ^ 2 ∂μ) ≤
      κ * ((14103 / 10000 : ℝ) * Real.sqrt (xi'' M h m / 2)) := by
    calc _ ≤ Real.sqrt (κ ^ 2 * ((14103 / 10000 : ℝ) ^ 2 * xi'' M h m / 2)) :=
          Real.sqrt_le_sqrt hYint
      _ = κ * ((14103 / 10000 : ℝ) * Real.sqrt (xi'' M h m / 2)) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hκ0,
          show (14103 / 10000 : ℝ) ^ 2 * xi'' M h m / 2 = (14103 / 10000 : ℝ) ^ 2 * (xi'' M h m / 2) by ring,
          Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by norm_num)]
  have hsum : (Real.sqrt (∫ ω, X ω ^ 2 ∂μ) + Real.sqrt (∫ ω, Y ω ^ 2 ∂μ)) ^ 2 ≤
      (|(CC).amp| * L + κ * ((14103 / 10000 : ℝ) * Real.sqrt (xi'' M h m / 2))) ^ 2 :=
    pow_le_pow_left₀ (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (add_le_add hsX hsY) 2
  refine hΛle.trans (hint.2.trans (hsum.trans (le_of_eq ?_)))
  unfold defectLambda
  rw [hκ]
  have hab2 : |(CC).amp| ^ 2 = (CC).amp ^ 2 := sq_abs _
  calc (|(CC).amp| * L + (44 / 25 : ℝ) * defectA * |(CC).amp| *
        ((14103 / 10000 : ℝ) * Real.sqrt (xi'' M h m / 2))) ^ 2
      = |(CC).amp| ^ 2 * (L + (44 / 25 : ℝ) * (14103 / 10000 : ℝ) * defectA *
        Real.sqrt (xi'' M h m / 2)) ^ 2 := by ring
    _ = _ := by rw [hab2]

end Budget

end

end ASDExplicitGamma.Scalar
