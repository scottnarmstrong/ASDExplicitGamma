module

public import ASDExplicitGamma.Scalar.GSlotMeas

/-! Joint measurability of the tiled positive-Haar energy of the potential-slot Wick source,
and of the weak budget `Λ_G`. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory Filter ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
  ASDExplicitGamma.Gaussian ASDExplicitGamma.Native
open scoped BigOperators Topology InnerProductSpace ENNReal

noncomputable section

variable (nQ : ℤ) (m : ℕ) (b : ℝ) (L : {l : ℝ // 0 < l})

local notation "QQ" => originCube 2 nQ

theorem openMeasurable :
    OpensMeasurableSpace (HilbertVectorL2 (openCubeSet QQ) × HilbertVectorL2 (openCubeSet QQ)) := by
  letI : IsSeparable (volumeMeasureOn (openCubeSet QQ)) := inferInstance
  letI : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  letI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
  have h2 : SecondCountableTopology (HilbertVectorL2 (openCubeSet QQ)) := inferInstance
  infer_instance

theorem gsymDefect_measurable {𝒪 : Type*} [MeasurableSpace 𝒪] {n : ℕ}
    (e : Fin n → Option whiteBasisIndex)
    (δ : Fin n → 𝒪 → HilbertVectorL2 (openCubeSet QQ)) (hδ : ∀ j, Measurable (δ j)) :
    Measurable (fun p : 𝒪 × (ℕ → ℝ) =>
      tiledPositiveEnergy QQ m (psdDefectSource
        (gSymRows nQ m b L e (fun j => rep2 nQ m (δ j p.1))) (fun i : Fin n => p.2 i))) := by
  haveI := openMeasurable nQ
  refine measurable_of_tendsto_metrizable (f := fun N (p : 𝒪 × (ℕ → ℝ)) =>
    (tiledPartialForm QQ m N).form
      (psdDefectSource (gSymRows nQ m b L e (fun j => rep2 nQ m (δ j p.1)))
        (fun i : Fin n => p.2 i))
      (psdDefectSource (gSymRows nQ m b L e (fun j => rep2 nQ m (δ j p.1)))
        (fun i : Fin n => p.2 i))) (fun N => ?_) ?_
  · simp only [psdDefectSource_form_expansion]
    refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
      Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun l _ => ?_
    have hy : ∀ i : Fin n, Measurable fun p : 𝒪 × (ℕ → ℝ) => p.2 (i : ℕ) :=
      fun i => (measurable_pi_apply (i : ℕ)).comp measurable_snd
    refine Measurable.mul (?_ : Measurable fun p : 𝒪 × (ℕ → ℝ) => _)
      ((((hy i).mul (hy j)).mul ((hy k).mul (hy l))))
    have key : ∀ (ea ec : Option whiteBasisIndex) (a c : Fin n),
        Measurable fun p : 𝒪 × (ℕ → ℝ) =>
          (tiledPartialForm QQ m N).form
            (gSlotOpt nQ m b L ea (rep2 nQ m (δ a p.1)))
            (gSlotOpt nQ m b L ec (rep2 nQ m (δ c p.1))) := by
      intro ea ec a c
      have hc : Measurable (fun q : HilbertVectorL2 (openCubeSet QQ) × HilbertVectorL2 (openCubeSet QQ) =>
          (tiledPartialForm QQ m N).form (gSlotOpt nQ m b L ea (rep2 nQ m q.1))
            (gSlotOpt nQ m b L ec (rep2 nQ m q.2))) :=
        (gcoef_continuous nQ m b L N ea ec).measurable
      have hp : Measurable fun p : 𝒪 × (ℕ → ℝ) => (δ a p.1, δ c p.1) :=
        ((hδ a).comp measurable_fst).prodMk ((hδ c).comp measurable_fst)
      have hcomp := hc.comp hp
      exact hcomp
    simp only [gSymRows, map_smul, map_add, LinearMap.smul_apply, LinearMap.add_apply,
      smul_eq_mul]
    exact ((((key (e i) (e k) j l).add (key (e j) (e k) i l)).const_mul (1 / 2 : ℝ)).add
      (((key (e i) (e l) j k).add (key (e j) (e l) i k)).const_mul (1 / 2 : ℝ))).const_mul
      (1 / 2 : ℝ)
  · rw [tendsto_pi_nhds]
    intro p
    exact tiledPartialForm_tendsto QQ m _

/-- The weak budget `∑_j W(δ_j)` is a continuous function of the `L²` classes. -/
theorem gLambda_measurable {𝒪 : Type*} [MeasurableSpace 𝒪] {n : ℕ}
    (δ : Fin n → 𝒪 → HilbertVectorL2 (openCubeSet QQ)) (hδ : ∀ j, Measurable (δ j)) :
    Measurable (fun o => ∑ j, lemmaVTiledWeakEnergy QQ m (rep2 nQ m (δ j o)).1) := by
  have hc : Continuous (fun u : HilbertVectorL2 (openCubeSet QQ) =>
      lemmaVTiledWeakEnergy QQ m (rep2 nQ m u).1) := by
    have : (fun u : HilbertVectorL2 (openCubeSet QQ) =>
        lemmaVTiledWeakEnergy QQ m (rep2 nQ m u).1) = fun u => ‖gSlotTheta nQ m u‖ ^ 2 := by
      funext u; exact (theta_norm_sq nQ m u).symm
    rw [this]
    exact ((theta_continuous nQ m).norm).pow 2
  exact Finset.measurable_sum _ fun j _ => hc.measurable.comp (hδ j)

end

end ASDExplicitGamma.Scalar
