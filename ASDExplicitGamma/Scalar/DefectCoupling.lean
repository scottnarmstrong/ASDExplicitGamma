module

public import ASDExplicitGamma.Gaussian.SeriesHeat
public import ASDExplicitGamma.Scalar.ChaosInfiniteInputMap
public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Topology.MetricSpace.Polish

/-! Coordinate extension: a sample space carrying a random element `f` of a Polish space,
independent of `o`, whose law is the image of the Gaussian product law under a measurable
`Z`, is extended by Gaussian coordinates `z` with `Z z = f`. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open MeasureTheory ProbabilityTheory ASDExplicitGamma.Gaussian
open scoped ENNReal

theorem coordinate_extension {Ω 𝒪 F : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒪]
    [TopologicalSpace F] [PolishSpace F] [MeasurableSpace F] [BorelSpace F]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (o : Ω → 𝒪) (f : Ω → F)
    (ho : Measurable o) (hf : Measurable f) (hind : IndepFun o f μ)
    (Z : (ℕ → ℝ) → F) (hZ : Measurable Z)
    (hlaw : standardGaussianInfinitePi.map Z = μ.map f) :
    ∃ μ' : Measure (Ω × (ℕ → ℝ)), IsProbabilityMeasure μ' ∧ μ'.map Prod.fst = μ ∧
      (∀ᵐ p ∂μ', Z p.2 = f p.1) ∧
      μ'.map (fun p => (o p.1, p.2)) = (μ.map o).prod standardGaussianInfinitePi := by
  set γ := standardGaussianInfinitePi
  haveI : IsProbabilityMeasure γ := instStandardGaussianInfinitePiProbability
  let κ0 : Kernel F (ℕ → ℝ) := condDistrib id Z γ
  let κ : Kernel Ω (ℕ → ℝ) := κ0.comap f hf
  have hcomp : (γ.map Z) ⊗ₘ κ0 = γ.map (fun z => (Z z, z)) :=
    compProd_map_condDistrib (μ := γ) hZ.aemeasurable (measurable_id (α := ℕ → ℝ)).aemeasurable
  have hlawb : γ.map Z = μ.map f := hlaw
  refine ⟨μ ⊗ₘ κ, inferInstance, Measure.fst_compProd μ κ, ?_, ?_⟩
  · -- almost sure identification
    let S : Set (F × (ℕ → ℝ)) := {q | Z q.2 ≠ q.1}
    have hS : MeasurableSet S :=
      (measurableSet_eq_fun (hZ.comp measurable_snd) measurable_fst).compl
    have h0 : ((γ.map Z) ⊗ₘ κ0) S = 0 := by
      rw [hcomp, Measure.map_apply (by fun_prop) hS]
      have : (fun z => (Z z, z)) ⁻¹' S = ∅ := by
        ext z; simp [S]
      rw [this]; simp
    rw [Measure.compProd_apply hS] at h0
    have hmeas : Measurable fun x => κ0 x (Prod.mk x ⁻¹' S) :=
      Kernel.measurable_kernel_prodMk_left hS
    have hae : ∀ᵐ x ∂(γ.map Z), κ0 x (Prod.mk x ⁻¹' S) = 0 :=
      (lintegral_eq_zero_iff hmeas).1 h0
    rw [hlawb] at hae
    have hae' : ∀ᵐ ω ∂μ, κ0 (f ω) (Prod.mk (f ω) ⁻¹' S) = 0 :=
      ae_of_ae_map hf.aemeasurable hae
    have hset : MeasurableSet {p : Ω × (ℕ → ℝ) | Z p.2 = f p.1} :=
      measurableSet_eq_fun (hZ.comp measurable_snd) (hf.comp measurable_fst)
    rw [Measure.ae_compProd_iff hset]
    filter_upwards [hae'] with ω hω
    have : κ ω = κ0 (f ω) := by simp [κ, Kernel.comap_apply]
    rw [this]
    rw [measure_eq_zero_iff_ae_notMem] at hω
    filter_upwards [hω] with b hb
    by_contra hne
    exact hb (by simpa [S] using hne)
  · -- law of (o, z)
    have hg : Measurable (fun p : Ω × (ℕ → ℝ) => (o p.1, p.2)) :=
      (ho.comp measurable_fst).prodMk measurable_snd
    symm
    refine Measure.prod_eq fun s t hs ht => ?_
    rw [Measure.map_apply hg (hs.prod ht)]
    have hpre : (fun p : Ω × (ℕ → ℝ) => (o p.1, p.2)) ⁻¹' (s ×ˢ t) = (o ⁻¹' s) ×ˢ t := by
      ext p; simp
    rw [hpre, Measure.compProd_apply_prod (ho hs) ht, Measure.map_apply ho hs]
    have hG : Measurable fun x => κ0 x t := Kernel.measurable_coe κ0 ht
    have hκt : ∀ ω, κ ω t = κ0 (f ω) t := fun ω => by simp [κ, Kernel.comap_apply]
    simp_rw [hκt]
    have hA : MeasurableSet (o ⁻¹' s) := ho hs
    have hφ1 : Measurable fun ω => (o ⁻¹' s).indicator (fun _ => (1 : ℝ≥0∞)) ω :=
      measurable_const.indicator hA
    have hφ2 : Measurable fun ω => κ0 (f ω) t := hG.comp hf
    have hind' : IndepFun (fun ω => (o ⁻¹' s).indicator (fun _ => (1 : ℝ≥0∞)) ω)
        (fun ω => κ0 (f ω) t) μ := by
      have h1 : Measurable fun a : 𝒪 => s.indicator (fun _ => (1 : ℝ≥0∞)) a :=
        measurable_const.indicator hs
      have e : (fun ω => (o ⁻¹' s).indicator (fun _ => (1 : ℝ≥0∞)) ω) =
          (fun a : 𝒪 => s.indicator (fun _ => (1 : ℝ≥0∞)) a) ∘ o := by
        funext ω
        by_cases h : o ω ∈ s <;> simp [Set.indicator, h]
      rw [e]
      exact hind.comp h1 hG
    have hmul := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun' hφ1.aemeasurable
      hφ2.aemeasurable hind'
    simp only [Pi.mul_apply] at hmul
    have e1 : ∫⁻ ω in o ⁻¹' s, κ0 (f ω) t ∂μ =
        ∫⁻ ω, (o ⁻¹' s).indicator (fun _ => (1 : ℝ≥0∞)) ω * κ0 (f ω) t ∂μ := by
      rw [← lintegral_indicator hA]
      refine lintegral_congr fun ω => ?_
      by_cases h : ω ∈ o ⁻¹' s <;> simp [Set.indicator, h]
    have e2 : ∫⁻ ω, κ0 (f ω) t ∂μ = γ t := by
      rw [← lintegral_map hG hf, ← hlawb]
      have := Measure.compProd_apply_prod (μ := γ.map Z) (κ := κ0) MeasurableSet.univ ht
      rw [hcomp, Measure.map_apply (by fun_prop) (MeasurableSet.univ.prod ht)] at this
      have hpre : (fun z => (Z z, z)) ⁻¹' (Set.univ ×ˢ t) = t := by ext z; simp
      rw [hpre] at this
      simp only [Measure.restrict_univ] at this
      exact this.symm
    rw [e1, hmul, e2, lintegral_indicator_const hA, one_mul]

end ASDExplicitGamma.Scalar
