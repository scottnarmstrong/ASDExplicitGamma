module

public import ASDExplicitGamma.Scalar.FlatQbigGauss
public import ASDExplicitGamma.Scalar.FlatSourceQ3ActualL128
public import ASDExplicitGamma.Triadic.VectorHaarSymmetry

/-! Q_big flat successor: the tiled positive Haar energy of the actual Wick product, by
transfer of the fixed-series bounds along the actual shell law. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Homogenization Filter
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped ENNReal Topology

namespace ASDExplicitGamma.Scalar

noncomputable section

local instance lawFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- Quarter-turn invariance of the tiled positive Haar energy of a Hilbert field. -/
theorem tiled_rot_eq (Q : TriadicCube 2) (n : ℕ) (W : HilbertVectorL2 (openCubeSet Q)) :
    lemmaVTiledPositiveEnergy Q n (fun x =>
      planarQuarterTurn (hilbertVectorL2ToVectorL2 (U := openCubeSet Q) W x)) =
      phi' Q n W := by
  unfold lemmaVTiledPositiveEnergy descendantsAverage phi'
  dsimp only
  congr 1
  refine Finset.sum_congr rfl fun R hR => ?_
  have h1 : vectorPositiveHaarEnergy R (fun x =>
      planarQuarterTurn (hilbertVectorL2ToVectorL2 (U := openCubeSet Q) W x)) =
      vectorPositiveHaarEnergy R (fun x i =>
        (hilbertVectorL2ToVectorL2 (U := openCubeSet Q) W x) i) := by
    rw [vecEnergy_eq_norm_sq, vecEnergy_eq_norm_sq]
    exact congrArg (· ^ 2) (vectorPositiveHaarNorm_quarterTurn R
      (fun x i => (hilbertVectorL2ToVectorL2 (U := openCubeSet Q) W x) i))
  rw [h1]
  apply vecEnergy_congr_ae
  intro i
  exact ae_descendant hR (hilbertVectorL2_normalizedCoordCLM_ae Q i W).symm

variable {a₀ b₀ c₀ d₀ : ℝ}

/-- The tiled energy of the actual Wick product: measurable, and its expectation and
`L^(128/127)` norm equal those of the fixed series product. -/
theorem actual_tiled_law (Q : TriadicCube 2) (hab : a₀ < b₀) (hcd : c₀ < d₀)
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (e : Vec 2) (k : ℤ) :
    Measurable (fun ω : Cutoff.CutoffSample 2 =>
      phi' Q 134 (flatSourceQ3ActualWickRepresentative Q hab hcd e k ω)) ∧
    (∫⁻ ω, ENNReal.ofReal (phi' Q 134
        (flatSourceQ3ActualWickRepresentative Q hab hcd e k ω))
        ∂(Cutoff.cutoffSampleLaw M).toMeasure =
      ∫⁻ ω, ENNReal.ofReal (phi' Q 134 (vfix Q hab hcd (q3ModelAmplitude M h k)
        (q3ModelLength k) e ω)) ∂standardGaussianInfinitePi) ∧
    (eLpNorm (fun ω => phi' Q 134
        (flatSourceQ3ActualWickRepresentative Q hab hcd e k ω))
        (ENNReal.ofReal (128 / 127 : ℝ)) (Cutoff.cutoffSampleLaw M).toMeasure =
      eLpNorm (fun ω => phi' Q 134 (vfix Q hab hcd (q3ModelAmplitude M h k)
        (q3ModelLength k) e ω)) (ENNReal.ofReal (128 / 127 : ℝ)) standardGaussianInfinitePi) := by
  classical
  let β := q3ModelAmplitude M h k
  let L := q3ModelLength k
  let K := closedRectangle a₀ b₀ c₀ d₀
  let μx := volumeMeasureOn (openCubeSet Q)
  let scalar : C(K, ℝ) →L[ℝ] Lp ℝ ∞ μx := flatSourceQ3ShellValueLInf Q hab hcd
  let projected : C(K, ℝ) →L[ℝ] HilbertVectorL2 (openCubeSet Q) :=
    lambda8Q3ProjectedLoadClass (isOpenBoundedConvexDomain_openCubeSet Q)
      a₀ b₀ c₀ d₀ hab hcd e
  let product : C(K, ℝ) → HilbertVectorL2 (openCubeSet Q) :=
    fun z => scalar z • projected z
  let energy : C(K, ℝ) → ℝ := fun z => phi' Q 134 (product z)
  let actualField : Cutoff.CutoffSample 2 → C(K, ℝ) := fun ω =>
    shellFieldScalarRestriction K (ω.1 k)
  let seriesField : (ℕ → ℝ) → C(K, ℝ) := fun ω =>
    q3C1Series a₀ b₀ c₀ d₀ β L whiteBasis ω 0
  have hproduct : Continuous product := by
    rw [continuous_iff_seqContinuous]
    intro zseq z hz
    have hf : Tendsto (fun n => scalar (zseq n)) atTop (𝓝 (scalar z)) :=
      (scalar.continuous.tendsto z).comp hz
    have hg : Tendsto (fun n => projected (zseq n)) atTop (𝓝 (projected z)) :=
      (projected.continuous.tendsto z).comp hz
    exact lp_product_tendsto_of_tendsto μx _ _ _ _ hf hg
  have henergy : Measurable energy :=
    Phi_measurable_of_V Q 134 product hproduct.measurable
  have hactual : Measurable actualField :=
    (measurable_shellFieldScalarRestriction K).comp
      ((measurable_pi_apply k).comp measurable_subtype_coe)
  have hseries : Measurable seriesField :=
    (continuous_apply 0).measurable.comp
      (stronglyMeasurable_q3C1Series a₀ b₀ c₀ d₀ β L whiteBasis).measurable
  have hscalar (z : Q3H3Range a₀ b₀ c₀ d₀ β L) :
      scalar (q3H3RangeC1 a₀ b₀ c₀ d₀ β L z 0) =
        flatSourceQ3ValueLInf Q hab hcd β L z := rfl
  have hprojected (z : Q3H3Range a₀ b₀ c₀ d₀ β L) :
      projected (q3H3RangeC1 a₀ b₀ c₀ d₀ β L z 0) =
        flatSourceQ3ProjectedL2 Q hab hcd e β L z := rfl
  have hseriesE : (fun ω => phi' Q 134 (vfix Q hab hcd β L e ω)) =
      fun ω => energy (seriesField ω) := by
    funext ω
    change _ = phi' Q 134 (scalar (q3H3RangeC1 a₀ b₀ c₀ d₀ β L
        (q3H3Series a₀ b₀ c₀ d₀ β L whiteBasis ω) 0) •
      projected (q3H3RangeC1 a₀ b₀ c₀ d₀ β L
        (q3H3Series a₀ b₀ c₀ d₀ β L whiteBasis ω) 0))
    rw [hscalar, hprojected]
    rfl
  have hactualE : (fun ω : Cutoff.CutoffSample 2 =>
      phi' Q 134 (flatSourceQ3ActualWickRepresentative Q hab hcd e k ω)) =
      fun ω => energy (actualField ω) := rfl
  have hlaw := actualShellLaw_eq_h3Series a₀ b₀ c₀ d₀ hab hcd M h hM k
  refine ⟨?_, ?_, ?_⟩
  · rw [hactualE]; exact henergy.comp hactual
  · simp only [fun ω => congrFun hseriesE ω, fun ω => congrFun hactualE ω]
    calc
      _ = ∫⁻ x, ENNReal.ofReal (energy x)
          ∂((Cutoff.cutoffSampleLaw M).toMeasure.map actualField) :=
        (lintegral_map (ENNReal.measurable_ofReal.comp henergy) hactual).symm
      _ = ∫⁻ x, ENNReal.ofReal (energy x) ∂(standardGaussianInfinitePi.map seriesField) := by
        rw [hlaw]
      _ = _ := lintegral_map (ENNReal.measurable_ofReal.comp henergy) hseries
  · rw [hseriesE, hactualE]
    have h1 := eLpNorm_map_measure (p := ENNReal.ofReal (128 / 127 : ℝ))
      (μ := (Cutoff.cutoffSampleLaw M).toMeasure) (f := actualField) (g := energy)
      henergy.aestronglyMeasurable hactual.aemeasurable
    have h2 := eLpNorm_map_measure (p := ENNReal.ofReal (128 / 127 : ℝ))
      (μ := standardGaussianInfinitePi) (f := seriesField) (g := energy)
      henergy.aestronglyMeasurable hseries.aemeasurable
    calc
      _ = eLpNorm energy (ENNReal.ofReal (128 / 127 : ℝ))
          ((Cutoff.cutoffSampleLaw M).toMeasure.map actualField) := h1.symm
      _ = eLpNorm energy (ENNReal.ofReal (128 / 127 : ℝ))
          (standardGaussianInfinitePi.map seriesField) := by rw [hlaw]
      _ = _ := h2

end

end ASDExplicitGamma.Scalar
