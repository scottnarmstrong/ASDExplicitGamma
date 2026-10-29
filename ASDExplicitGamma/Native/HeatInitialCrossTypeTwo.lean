module

public import ASDExplicitGamma.Native.HeatInitialCross
public import ASDExplicitGamma.Gaussian.Rio
public import ASDExplicitGamma.Model.Cutoff

/-! Fiberwise nine-colour type-two estimates for the native heat cross term. -/

@[expose] public section
noncomputable section

namespace ASDExplicitGamma.Native

open MeasureTheory ProbabilityTheory
open Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Numerics.Native
open scoped BigOperators ENNReal

/-- Integrate a fixed-fresh-vector moment bound over the fresh law. This is the
Tonelli step that turns the conditional square sum into the source Q moment. -/
theorem nativeHeat_product_moment_of_fiber_bounds
    {Ω Η : Type*} [MeasurableSpace Ω] [MeasurableSpace Η]
    {μ : Measure Ω} {ν : Measure Η} [SFinite μ] [SFinite ν]
    (F : Ω × Η → ℝ) (hF : Measurable F) (p : ℝ) (A : ℝ≥0∞)
    (q : Η → ℝ≥0∞) (hq : Measurable q)
    (hfiber : ∀ η, ∫⁻ ω, ‖F (ω, η)‖ₑ ^ p ∂μ ≤ A * q η) :
    ∫⁻ z, ‖F z‖ₑ ^ p ∂μ.prod ν ≤ A * ∫⁻ η, q η ∂ν := by
  let g : Ω × Η → ℝ≥0∞ := fun z => ‖F z‖ₑ ^ p
  have hg : Measurable g := by fun_prop
  let gcurried : Ω → Η → ℝ≥0∞ := fun ω η => g (ω, η)
  have hgc : AEMeasurable (Function.uncurry gcurried) (μ.prod ν) := by
    exact hg.aemeasurable
  calc
    _ = ∫⁻ η, ∫⁻ ω, g (ω, η) ∂μ ∂ν := by
      calc
        _ = ∫⁻ ω, ∫⁻ η, g (ω, η) ∂ν ∂μ := (lintegral_lintegral hgc).symm
        _ = ∫⁻ η, ∫⁻ ω, g (ω, η) ∂μ ∂ν := lintegral_lintegral_swap hgc
    _ ≤ ∫⁻ η, A * q η ∂ν := lintegral_mono hfiber
    _ = A * ∫⁻ η, q η ∂ν := lintegral_const_mul A hq

/-- Transfer a fixed old/fresh product-moment estimate back to the original
sample whenever the old and fresh observables are independent. -/
theorem nativeHeat_independent_pair_moment_eq_product
    {Ξ Ω Η : Type*} [MeasurableSpace Ξ] [MeasurableSpace Ω] [MeasurableSpace Η]
    {ρ : Measure Ξ} [IsProbabilityMeasure ρ]
    (X : Ξ → Ω) (G : Ξ → Η) (hX : Measurable X) (hG : Measurable G)
    (hIndep : IndepFun X G ρ) (F : Ω × Η → ℝ) (hF : Measurable F) (p : ℝ) :
    ∫⁻ ξ, ‖F (X ξ, G ξ)‖ₑ ^ p ∂ρ =
      ∫⁻ z, ‖F z‖ₑ ^ p ∂(ρ.map X).prod (ρ.map G) := by
  let P : Ξ → Ω × Η := fun ξ => (X ξ, G ξ)
  let q : Ω × Η → ℝ≥0∞ := fun z => ‖F z‖ₑ ^ p
  have hP : Measurable P := hX.prodMk hG
  have hq : Measurable q := by fun_prop
  calc
    _ = ∫⁻ z, q z ∂ρ.map P := by
      symm
      simpa [P, q] using lintegral_map hq hP
    _ = ∫⁻ z, q z ∂(ρ.map X).prod (ρ.map G) := by
      rw [hIndep.map_prod_eq_prod_map_map hX.aemeasurable hG.aemeasurable]
    _ = _ := rfl

/-- The completed old cutoff information is independent of any disjoint block
of fresh shell coordinates, on the literal cutoff probability carrier. -/
theorem nativeHeat_cutoffLocal_freshBlock_independent
    {Ω Η : Type*} [MeasurableSpace Ω] [MeasurableSpace Η]
    (M : ABKModel 2) (mOld : ℤ) (J : Set ℤ)
    (hJ : Disjoint (Set.Iic mOld) J)
    (X : Cutoff.CutoffSample 2 → Ω)
    (hX : @Measurable (Cutoff.CutoffSample 2) Ω
      (Cutoff.cutoffSampleLocalSigma M mOld Set.univ) _ X)
    (G : Cutoff.CutoffSample 2 → Η)
    (hG : @Measurable (Cutoff.CutoffSample 2) Η
      ((Cutoff.shellIndexSigma J).comap Subtype.val) _ G) :
    IndepFun X G (Cutoff.cutoffSampleLaw M).toMeasure := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  have hseq := Cutoff.indep_lowerShellLocalCompletion_shellIndexSigma_of_disjoint
    M hJ Set.univ
  have hsig : Indep (Cutoff.cutoffSampleLocalSigma M mOld Set.univ)
      ((Cutoff.shellIndexSigma J).comap Subtype.val) μ := by
    rw [Indep_iff]
    intro s t hs ht
    rcases MeasurableSpace.measurableSet_comap.mp hs with ⟨s', hs', rfl⟩
    rcases MeasurableSpace.measurableSet_comap.mp ht with ⟨t', ht', rfl⟩
    obtain ⟨s₀, hs₀, hs'₀⟩ := hs'
    have hs₀Borel : MeasurableSet s₀ :=
      Cutoff.lowerShellLocalSigma_le_borel mOld Set.univ s₀ hs₀
    have htBorel : MeasurableSet t' := (Cutoff.shellIndexSigma_le_borel J) t' ht'
    have hsCut : (Subtype.val : Cutoff.CutoffSample 2 → Cutoff.ShellSeq 2) ⁻¹' s' =ᵐ[μ]
        (Subtype.val : Cutoff.CutoffSample 2 → Cutoff.ShellSeq 2) ⁻¹' s₀ := by
      rw [← Cutoff.map_cutoffSampleLaw_val M] at hs'₀
      exact (Measure.tendsto_ae_map measurable_subtype_coe.aemeasurable).eventually hs'₀
    have hstCut : (Subtype.val : Cutoff.CutoffSample 2 → Cutoff.ShellSeq 2) ⁻¹'
        (s' ∩ t') =ᵐ[μ]
        (Subtype.val : Cutoff.CutoffSample 2 → Cutoff.ShellSeq 2) ⁻¹' (s₀ ∩ t') := by
      simpa only [Set.preimage_inter] using hsCut.inter Filter.EventuallyEq.rfl
    have hmap (u : Set (Cutoff.ShellSeq 2)) (hu : MeasurableSet u) :
        μ ((Subtype.val : Cutoff.CutoffSample 2 → Cutoff.ShellSeq 2) ⁻¹' u) =
          M.P.toMeasure u := by
      rw [← Measure.map_apply_of_aemeasurable measurable_subtype_coe.aemeasurable hu,
        Cutoff.map_cutoffSampleLaw_val]
    rw [← Set.preimage_inter, measure_congr hstCut, measure_congr hsCut,
      hmap (s₀ ∩ t') (hs₀Borel.inter htBorel), hmap s₀ hs₀Borel, hmap t' htBorel]
    exact (Indep_iff _ _ M.P.toMeasure).mp hseq s₀ t'
      ⟨s₀, hs₀, Filter.EventuallyEq.rfl⟩ ht'
  exact (ProbabilityTheory.IndepFun_iff_Indep X G μ).mpr
    (ProbabilityTheory.indep_of_indep_of_le_right
      (ProbabilityTheory.indep_of_indep_of_le_left hsig hX.comap_le)
      hG.comap_le)

/-- Translation-invariant block symmetry centers every actual old child shear. -/
theorem nativeHeat_oldShear_centered
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2)
    (htrace : MemLp (Cold.coldNativeCellTrace M m Q) 2
      (Cutoff.cutoffSampleLaw M).toMeasure) :
    ∫ ω, Variational.shearTraceLinear (coarseBlockMatrix (cubeSet Q)
      (Cutoff.coefficientCutoff M.nu m ω).toFun)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure = 0 := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  obtain ⟨p, q, hp, hq, hmean⟩ := Cold.coldNativeResponse_mean_blocks M m Q
  have h01 : (Cold.matrixMean μ (Cold.coldNativeResponse M m Q))
      (Sum.inl 1) (Sum.inr 0) = 0 := by
    rw [hmean]
    simp [Cold.coldGraphBlockMean, Homogenization.toFullBlockMat, Book.Ch02.blockDiag]
  have h10 : (Cold.matrixMean μ (Cold.coldNativeResponse M m Q))
      (Sum.inl 0) (Sum.inr 1) = 0 := by
    rw [hmean]
    simp [Cold.coldGraphBlockMean, Homogenization.toFullBlockMat, Book.Ch02.blockDiag]
  have hmean01 : ∫ ω, Cold.coldNativeResponse M m Q ω
      (Sum.inl 1) (Sum.inr 0) ∂μ = 0 := by
    simpa [Cold.matrixMean] using h01
  have hmean10 : ∫ ω, Cold.coldNativeResponse M m Q ω
      (Sum.inl 0) (Sum.inr 1) ∂μ = 0 := by
    simpa [Cold.matrixMean] using h10
  have hint01 : Integrable (fun ω => Cold.coldNativeResponse M m Q ω
      (Sum.inl 1) (Sum.inr 0)) μ := by
    exact (Cold.coldNativeResponse_memLp_of_trace M m Q htrace
      (Sum.inl 1) (Sum.inr 0)).integrable (by norm_num)
  have hint10 : Integrable (fun ω => Cold.coldNativeResponse M m Q ω
      (Sum.inl 0) (Sum.inr 1)) μ := by
    exact (Cold.coldNativeResponse_memLp_of_trace M m Q htrace
      (Sum.inl 0) (Sum.inr 1)).integrable (by norm_num)
  have hshear (ω : Cutoff.CutoffSample 2) :
      Variational.shearTraceLinear (coarseBlockMatrix (cubeSet Q)
        (Cutoff.coefficientCutoff M.nu m ω).toFun) =
      Cold.coldNativeResponse M m Q ω (Sum.inl 1) (Sum.inr 0) -
        Cold.coldNativeResponse M m Q ω (Sum.inl 0) (Sum.inr 1) := by
    simp [Cold.coldNativeResponse, Variational.shearTraceLinear,
      Variational.frameMatrix, Homogenization.toFullBlockMat]
  calc
    _ = ∫ ω, (Cold.coldNativeResponse M m Q ω (Sum.inl 1) (Sum.inr 0) -
        Cold.coldNativeResponse M m Q ω (Sum.inl 0) (Sum.inr 1)) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hshear
    _ = _ := by rw [integral_sub hint01 hint10, hmean01, hmean10, sub_self]

end ASDExplicitGamma.Native
