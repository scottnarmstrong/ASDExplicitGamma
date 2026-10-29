module

public import ASDExplicitGamma.Scalar.CombinePath
public import ASDExplicitGamma.Scalar.RefNodeRR

/-! Expectation of the flat-leg cross term (Cauchy-Schwarz over `Ω` through the defect family
theorem), and the named flat-leg hypothesis. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
open Algsuperdiff.Section3 ASDExplicitGamma.Native ASDExplicitGamma.Inverse Filter
open scoped InnerProductSpace BigOperators ENNReal Topology

attribute [local irreducible] Homogenization.descendantsAtDepth

noncomputable section

section Exp

variable (M : ABKModel 2) (h : ℝ) (m : ℤ) {a b c d : ℝ} (hab : a < b) (hcd : c < d)
  (hQ : openCubeSet (originCube 2 (m + 129)) ⊆ openRectangle a b c d) (e : Vec 2)

local notation "CC" => finalCfg M h m hab hcd hQ e

/-- The pathwise flat majorant `σ⁻⁴ · B* · PE(F_flat)` (the flat leg's diagonal is at most
`vol` times this). -/
def flatMajorant (ω : Cutoff.CutoffSample 2) : ℝ :=
  ((((CC).σ ^ 2)⁻¹ : ℝ) ^ 2) * (bnew M m (originCube 2 (m + 129)) ω *
    lemmaVTiledPositiveEnergy (originCube 2 (m + 129)) 134
      (Cfg''.flatField (originCube 2 (m + 129)) hab hcd e m ω))

/-- The named flat-leg hypothesis (expectation of the big-cube flat quantity `σ⁻⁴ B* PE(F_flat)`
against the NEW bank, normalized by `(amp²)²`): `Fflat` is a nonnegative bound for it. -/
def FlatExpectationBound (Fflat : ℝ) : Prop :=
  0 ≤ Fflat ∧ Measurable (flatMajorant M h m hab hcd hQ e) ∧
    Integrable (flatMajorant M h m hab hcd hQ e) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    ∫ ω, flatMajorant M h m hab hcd hQ e ω ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
      ((CC).amp ^ 2) ^ 2 * Fflat

theorem flatMajorant_nonneg (ω : Cutoff.CutoffSample 2) :
    0 ≤ flatMajorant M h m hab hcd hQ e ω :=
  mul_nonneg (sq_nonneg _) (mul_nonneg (bnew_nonneg M m _ ω)
    (lemmaVTiledPositiveEnergy_nonneg _ _ _))

theorem cross_expect_t (hM : PlanarQ3Gaussian M h) (hγ : M.gamma ≤ gammaZero)
    (hpast : ∀ n ≤ m, nativeInductionState M h n) (he : Book.Ch02.vecNorm e = 1)
    (he2 : vecNormSq e = 1) {Fflat : ℝ} (hF : FlatExpectationBound M h m hab hcd hQ e Fflat)
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun ω => max (2 * (CC).crossActR m ω) 0) (Cutoff.cutoffSampleLaw M).toMeasure ∧
      ∫ ω, max (2 * (CC).crossActR m ω) 0 ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤
        (volume (openCubeSet (originCube 2 (m + 129)))).toReal * (((CC).amp ^ 2) ^ 2 *
          ((141 / 100 : ℝ) * (t * Fflat + defectFdefR mainSourceMeanPrefix (xi'' M h m)
            (mStar' M) (14103 / 10000) (5 / 10 ^ 24) (14103 / 10000) (5 / 10 ^ 24)
            roughR / t))) := by
  obtain ⟨ell, hK⟩ := exists_originCube_containing_compact (closedRectangle a b c d)
    (closedRectangle_isCompact a b c d)
  obtain ⟨hF0, hFm, hFi, hFb⟩ := hF
  set μ := (Cutoff.cutoffSampleLaw M).toMeasure with hμ
  set vol := (volume (openCubeSet (originCube 2 (m + 129)))).toReal with hvol
  have hvol0 : 0 ≤ vol := ENNReal.toReal_nonneg
  set P := flatMajorant M h m hab hcd hQ e with hP
  have hP0 := flatMajorant_nonneg M h m hab hcd hQ e
  have hCm : Measurable (fun ω => t * ((141 / 100 : ℝ) * (vol * P ω))) :=
    (hFm.const_mul vol |>.const_mul (141 / 100 : ℝ)).const_mul t
  have hDnm : ∀ n, Measurable (fun p : Cutoff.CutoffSample 2 × (ℕ → ℝ) =>
      2 * (CC).crossTruncR m p.1 n (fun i : Fin n => p.2 i) -
        t * ((141 / 100 : ℝ) * (vol * P p.1))) := fun n =>
    (((CC).crossTruncR_measurable m ell hK n).const_mul 2).sub (hCm.comp measurable_fst)
  have hcm : Measurable (fun ω : Cutoff.CutoffSample 2 => 2 * (CC).crossActR m ω) :=
    ((CC).crossActR_measurable m ell hK).const_mul 2
  have hDωm : Measurable (fun ω => 2 * (CC).crossActR m ω -
      t * ((141 / 100 : ℝ) * (vol * P ω))) := hcm.sub hCm
  have hcross := defect_family_final M h m hab hcd hQ e hM hγ (fun n hn => hpast n hn.le)
    mainSourceMeanPrefix (xi'' M h m) (mStar' M) (5 / 10 ^ 24) roughR
    (by unfold roughR defectA; positivity)
    ((141 / 100 : ℝ) / t) (by positivity)
    (fun n p => 2 * (CC).crossTruncR m p.1 n (fun i : Fin n => p.2 i) -
      t * ((141 / 100 : ℝ) * (vol * P p.1)))
    (fun ω => 2 * (CC).crossActR m ω - t * ((141 / 100 : ℝ) * (vol * P ω)))
    hDnm hDωm
    (fun n => budget_Lam1T M h m hab hcd hQ e hM hγ hpast he he2 ell hK n)
    (fun n => budget_LamQ_rough M h m hab hcd hQ e hM hγ hpast he2 ell hK n)
    (fun n p => by
      have h1 := Cfg''.crossTruncR_amgm M h m hab hcd hQ e p.1 n (fun i : Fin n => p.2 i) ht
      rw [← hvol] at h1
      simp only [hP, flatMajorant]
      show (2 * (CC).crossTruncR m p.1 n (fun i : Fin n => p.2 i)) - _ ≤ (141 / 100 : ℝ) / t *
        ((volume (openCubeSet (originCube 2 (m + 129)))).toReal *
          (bnew M m (originCube 2 (m + 129)) p.1 *
            (tiledPositiveEnergy (originCube 2 (m + 129)) 134
              (psdDefectSource ((CC).BFoR ((CC).old m p.1) n) (fun i : Fin n => p.2 i)) +
             tiledPositiveEnergy (originCube 2 (m + 129)) 134
              (psdDefectSource ((CC).BGoR ((CC).old m p.1) n) (fun i : Fin n => p.2 i)))))
      rw [← hvol]
      linarith)
    (fun p hz hs => by
      have hs' : Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, p.2 i • (CC).Hs i)
          Filter.atTop (nhds ((CC).z0 m p.1)) := by rw [hz]; exact hs
      exact ((((CC).crossTruncR_tendsto m p.1 p.2 hs').const_mul 2).sub_const _))
    (sq_nonneg _)
  obtain ⟨hint, hbd⟩ := hcross
  have hC0 : ∀ ω, 0 ≤ t * ((141 / 100 : ℝ) * (vol * P ω)) := fun ω => by
    have := hP0 ω
    positivity
  have hCint : Integrable (fun ω => t * ((141 / 100 : ℝ) * (vol * P ω))) μ :=
    (hFi.const_mul vol |>.const_mul (141 / 100 : ℝ)).const_mul t
  have hle : ∀ ω, max (2 * (CC).crossActR m ω) 0 ≤
      max (2 * (CC).crossActR m ω - t * ((141 / 100 : ℝ) * (vol * P ω))) 0 +
        t * ((141 / 100 : ℝ) * (vol * P ω)) := fun ω => by
    have h0 := hC0 ω
    have h1 := le_max_left (2 * (CC).crossActR m ω - t * ((141 / 100 : ℝ) * (vol * P ω))) 0
    have h2 := le_max_right (2 * (CC).crossActR m ω - t * ((141 / 100 : ℝ) * (vol * P ω))) 0
    exact max_le (by linarith) (by linarith)
  have hint2 : Integrable (fun ω => max (2 * (CC).crossActR m ω) 0) μ :=
    (hint.add hCint).mono' (hcm.max measurable_const).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        exact hle ω)
  refine ⟨hint2, ?_⟩
  have h3 : ∫ ω, max (2 * (CC).crossActR m ω) 0 ∂μ ≤
      ∫ ω, (max (2 * (CC).crossActR m ω - t * ((141 / 100 : ℝ) * (vol * P ω))) 0 +
        t * ((141 / 100 : ℝ) * (vol * P ω))) ∂μ :=
    integral_mono hint2 (hint.add hCint) hle
  rw [integral_add hint hCint] at h3
  have h4 : ∫ ω, t * ((141 / 100 : ℝ) * (vol * P ω)) ∂μ =
      t * ((141 / 100 : ℝ) * (vol * ∫ ω, P ω ∂μ)) := by
    rw [integral_const_mul, integral_const_mul, integral_const_mul]
  rw [h4] at h3
  have h5 : t * ((141 / 100 : ℝ) * (vol * ∫ ω, P ω ∂μ)) ≤
      t * ((141 / 100 : ℝ) * (vol * (((CC).amp ^ 2) ^ 2 * Fflat))) := by
    gcongr
  refine h3.trans ((add_le_add hbd h5).trans (le_of_eq ?_))
  field_simp
  ring

end Exp

end

end ASDExplicitGamma.Scalar
