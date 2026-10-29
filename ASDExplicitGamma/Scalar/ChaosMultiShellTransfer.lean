module

public import ASDExplicitGamma.Gaussian.BandModelLaw
public import ASDExplicitGamma.Gaussian.ModelHeatLaw
public import Mathlib.MeasureTheory.Integral.Prod

/-! Joint OLD/future-band transfer through the actual finite-band realization. -/

@[expose] public section

open MeasureTheory ProbabilityTheory ASDExplicitGamma.Gaussian
  Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open Homogenization
open scoped ENNReal

namespace ASDExplicitGamma.Scalar

/-- The completed OLD field and any finite family of future physical shells have the
product law of the actual OLD marginal and one direct-sum Gaussian series.  Thus every
measurable OLD/fresh-band envelope has exactly the same eLpNorm under the cutoff law
as under this product realization. -/
theorem joint_old_multishell_eLpNorm_eq_ga_cm
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (ell m : ℤ) {K : Set (Homogenization.Vec 2)} [CompactSpace K]
    (hK : K ⊆ openCubeSet (originCube 2 ell))
    {b : ℕ} [NeZero b] (k : Fin b → ℤ)
    (hk : Function.Injective k) (hfuture : ∀ i, m < k i)
    (F : C(K, ℝ) × C(K, ℝ) → ℝ) (hF : Measurable F) (p : ℝ≥0∞) :
    ∃ (T : BandHilbert b →L[ℝ] C(K, ℝ))
      (v : ℕ → BandHilbert b)
      (hA : Summable (fun j => ‖v j‖ ^ 2)),
      (Cutoff.cutoffSampleLaw M).toMeasure.map (modelBand K k) =
        Gaussian.standardGaussianInfinitePi.map (gaussianSeriesLimitE hA T) ∧
      eLpNorm
          (fun ω : Cutoff.CutoffSample 2 =>
            F (olderField K m ω, modelBand K k ω))
          p (Cutoff.cutoffSampleLaw M).toMeasure =
        eLpNorm
          (fun z : C(K, ℝ) × (ℕ → ℝ) =>
            F (z.1, gaussianSeriesLimitE hA T z.2))
          p (((Cutoff.cutoffSampleLaw M).toMeasure.map (olderField K m)).prod
            Gaussian.standardGaussianInfinitePi) := by
  obtain ⟨T, v, hA, hlaw⟩ :=
    exists_modelBand_realization K M h hM k hk
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let X : Cutoff.CutoffSample 2 → C(K, ℝ) := olderField K m
  let Y : Cutoff.CutoffSample 2 → C(K, ℝ) := fun ω => modelBand K k ω
  let Z : (ℕ → ℝ) → C(K, ℝ) := gaussianSeriesLimitE hA T
  let pair : Cutoff.CutoffSample 2 → C(K, ℝ) × C(K, ℝ) := fun ω => (X ω, Y ω)
  let ν := μ.map X
  let gaussianPair : C(K, ℝ) × (ℕ → ℝ) → C(K, ℝ) × C(K, ℝ) :=
    fun z => (z.1, Z z.2)
  have hX : Measurable X := measurable_olderField K ell m hK
  have hY : Measurable Y := measurable_modelBand K k
  have hZ : Measurable Z :=
    (stronglyMeasurable_gaussianSeriesLimitE hA T).measurable
  have hpair : μ.map pair = ν.prod (Gaussian.standardGaussianInfinitePi.map Z) := by
    rw [← hlaw]
    exact (indepFun_olderField_band K M ell m hK k hfuture).map_prod_eq_prod_map_map
      hX.aemeasurable hY.aemeasurable
  have hprod : ν.prod (Gaussian.standardGaussianInfinitePi.map Z) =
      (ν.prod Gaussian.standardGaussianInfinitePi).map gaussianPair := by
    change ν.prod (Gaussian.standardGaussianInfinitePi.map Z) =
      (ν.prod Gaussian.standardGaussianInfinitePi).map (Prod.map id Z)
    simpa only [Measure.map_id] using
      Measure.map_prod_map ν Gaussian.standardGaussianInfinitePi measurable_id hZ
  have hpairMeas : Measurable pair := hX.prodMk hY
  have hgaussianPairMeas : Measurable gaussianPair := measurable_id.prodMap hZ
  have hleft := eLpNorm_map_measure (p := p) (μ := μ) (f := pair)
    hF.aestronglyMeasurable hpairMeas.aemeasurable
  have hright := eLpNorm_map_measure (p := p)
    (μ := ν.prod Gaussian.standardGaussianInfinitePi) (f := gaussianPair)
    hF.aestronglyMeasurable hgaussianPairMeas.aemeasurable
  refine ⟨T, v, hA, hlaw, ?_⟩
  calc
    _ = eLpNorm F p (μ.map pair) := hleft.symm
    _ = eLpNorm F p ((ν.prod Gaussian.standardGaussianInfinitePi).map gaussianPair) := by
      rw [hpair, hprod]
    _ = _ := hright

end ASDExplicitGamma.Scalar
