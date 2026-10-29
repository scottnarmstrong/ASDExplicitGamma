module

public import ASDExplicitGamma.Scalar.ParentComparison
public import ASDExplicitGamma.Scalar.TiledTrial

/-! A finite-parent comparison with the exact source cell energy and the
large-cube localized stream error. -/

@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory Response Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Corrector
noncomputable section

private theorem local_error_average_eq (M : ABKModel 2) (n N : ℤ) (σ : ℝ)
    (e : Vec 2) (Q : TriadicCube 2) (L : ℕ)
    (S : CutoffSample 2 → (Fin 2 → HilbertVec 2)) (D : CutoffSample 2 → HilbertVec 2)
    (ω : CutoffSample 2)
    (hErr : MemHilbertVectorL2 (cubeSet Q) (fun x =>
      HilbertVec.ofVec (localStreamApprox Q L S D ω x) -
        realize (cutoffBandFlux M n N σ⁻¹ e) ω x)) :
    volumeAverage (openCubeSet Q) (fun x => vecNormSq
      (localStreamApprox Q L S D ω x -
        (realize (cutoffBandFlux M n N σ⁻¹ e) ω x).toVec)) =
      cubeLpNorm Q 2 (fun x => HilbertVec.ofVec
        (localStreamApprox Q L S D ω x) -
          realize (cutoffBandFlux M n N σ⁻¹ e) ω x) ^ (2 : ℝ) := by
  let d : Vec 2 → Vec 2 := fun x => localStreamApprox Q L S D ω x -
    (realize (cutoffBandFlux M n N σ⁻¹ e) ω x).toVec
  have hfun : (fun x => HilbertVec.ofVec (d x)) =
      (fun x => HilbertVec.ofVec (localStreamApprox Q L S D ω x) -
        realize (cutoffBandFlux M n N σ⁻¹ e) ω x) := by
    funext x
    dsimp [d]
  have hErr' : MemHilbertVectorL2 (cubeSet Q) (fun x => HilbertVec.ofVec (d x)) := by
    rw [hfun]
    exact hErr
  calc
    volumeAverage (openCubeSet Q) (fun x => vecNormSq (d x)) =
        cubeAverage Q (fun x => vecNormSq (d x)) := by
      unfold volumeAverage cubeAverage
      rw [← setIntegral_cubeSet_eq_setIntegral_openCubeSet]
      rw [volume_openCubeSet_toReal]
    _ = cubeAverage Q (fun x => ‖HilbertVec.ofVec (d x)‖ ^ (2 : ℕ)) := by
      congr 1
      funext x
      rw [norm_sq_ofVec]
      rfl
    _ = cubeLpNorm Q 2 (fun x => HilbertVec.ofVec (d x)) ^ (2 : ℝ) :=
      (cubeLpNorm_two_rpow_eq_cubeAverage_norm_sq hErr').symm
    _ = cubeLpNorm Q 2 (fun x => HilbertVec.ofVec
          (localStreamApprox Q L S D ω x) -
            realize (cutoffBandFlux M n N σ⁻¹ e) ω x) ^ (2 : ℝ) := by
      rw [hfun]

/-- At every sufficiently large parent, an actual localized stream bounds the
annealed top quadratic by the exact source-cell energy plus its pure-flux
boundary error. -/
theorem localized_parent_bound (M : ABKModel 2) (n N q k : ℤ) (σ τ : ℝ)
    (hσ : 0 < σ) (hτ : 0 < τ) (e : Vec 2) (he : vecDot e e = 1)
    (C : CutoffSample 2 → Vec 2 → BlockVec 2)
    (hC : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      ScalarVariation (openCubeSet (originCube 2 q)) (C ω))
    (hE : Integrable (cutoffTrialEnergy M N σ (originCube 2 q)
      (bandTrialField M n N σ e C)) (Cutoff.cutoffSampleLaw M).toMeasure)
    (S : CutoffSample 2 → (Fin 2 → HilbertVec 2)) (D : CutoffSample 2 → HilbertVec 2)
    (L : ℕ)
    (hSm : StronglyMeasurable S) (hS : MemLp S 2 (Cutoff.cutoffSampleLaw M).toMeasure)
    (hDm : StronglyMeasurable D) (hD : MemLp D 2 (Cutoff.cutoffSampleLaw M).toMeasure)
    (hSmooth : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure, ∀ i j : Fin 2,
      ContDiff ℝ (⊤ : ℕ∞) (streamRealization S ω i j))
    (hAnti : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure, ∀ i j : Fin 2,
      streamRealization S ω j i = -streamRealization S ω i j)
    (hDiv : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure, ∀ x : Vec 2,
      streamDivergence (streamRealization S ω) x =
        (realize D ω x).toVec)
    (hq : q ≤ k) :
    σ⁻¹ * (Homogenization.Book.Ch04.annealedBlockMatrixAtScale
      (Cutoff.coefficientCutoffLaw M N) k).upperLeft 0 0 ≤
      (1+τ) * (∫ ω, cutoffTrialEnergy M N σ (originCube 2 q)
        (bandTrialField M n N σ e C) ω
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) +
      (1+τ⁻¹)*(σ/M.nu) *
        ∫ ω, cubeLpNorm (originCube 2 k) 2
          (fun x => HilbertVec.ofVec
            (localStreamApprox (originCube 2 k) L S D ω x) -
              realize (cutoffBandFlux M n N σ⁻¹ e) ω x) ^ (2 : ℝ)
          ∂(Cutoff.cutoffSampleLaw M).toMeasure := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let Q := originCube 2 k
  let j := cutoffBandFlux M n N σ⁻¹ e
  let err := fun ω => cubeLpNorm Q 2 (fun x =>
    HilbertVec.ofVec (localStreamApprox Q L S D ω x) - realize j ω x) ^ (2 : ℝ)
  let sourceEnergy := cutoffTrialEnergy M N σ (originCube 2 q)
    (bandTrialField M n N σ e C)
  let parentEnergy := cutoffTrialEnergy M N σ Q
    (tiledBandTrial M n N σ e C Q q)
  have hjm : StronglyMeasurable j := by
    exact stronglyMeasurable_cutoffBandFlux M n N σ⁻¹ e
  have hj : MemLp j 2 μ := by
    exact memLp_two_cutoffBandFlux M n N σ⁻¹ e
  have hApprox := ae_memLp_localStreamApprox_sub_of_approximateStream
    (μ := μ) Q L hSm hS hDm hD hjm hj
  have hErrInt := integrable_cubeLpNorm_localStreamApprox_sub_of_approximateStream
    (μ := μ) Q L hSm hS hDm hD hjm hj
  have hLocalL2 := ae_memVectorL2_localStreamApprox M n N σ⁻¹ e Q L S D
    hSm hS hDm hD
  have hCell : ∀ᵐ ω ∂μ, ∀ R, R ∈ descendantsAtScale Q q →
      ScalarVariation (openCubeSet R) (translatedCellCorrection C R ω) := by
    rw [ae_all_iff]
    intro R
    by_cases hR : R ∈ descendantsAtScale Q q
    · exact (ae_translated_correction M q C hC R
        (scale_eq_of_mem_descendantsAtScale hR)).mono
          (fun ω hω _ => hω)
    · exact Filter.Eventually.of_forall fun ω h => (hR h).elim
  have hData : ∀ᵐ ω ∂μ,
      (∀ i j : Fin 2, ContDiff ℝ (⊤ : ℕ∞) (streamRealization S ω i j)) ∧
      (∀ i j : Fin 2, streamRealization S ω j i = -streamRealization S ω i j) ∧
      (∀ x : Vec 2, streamDivergence (streamRealization S ω) x =
        (realize D ω x).toVec) := by
    filter_upwards [hSmooth, hAnti, hDiv] with ω hs ha hd
    exact ⟨hs, ha, hd⟩
  have hLocalVar : ∀ᵐ ω ∂μ, ScalarVariation (openCubeSet Q)
      (fun x => scalarBottomLoad (localStreamApprox Q L S D ω) x) := by
    filter_upwards [hLocalL2, hData] with ω hω hdata
    exact ⟨scalar_bottom_load_memL2 hω, isPotentialZeroTraceOn_zero,
      isSolenoidalZeroNormalTraceOn_localStreamApprox Q L
        hdata.1 hdata.2.1 hdata.2.2⟩
  have hTiled := integral_tiled_trial_energy M n N q σ hσ e C hC hE Q hq
  have hErrInt' : Integrable err μ := by
    exact hErrInt.congr (Filter.Eventually.of_forall fun ω => by rfl)
  have hTopInt := integrable_cutoff_top_quadratic M N k e
  have hParentInt : Integrable (fun ω => (1+τ)*parentEnergy ω) μ := by
    simpa [parentEnergy] using hTiled.1.const_mul (1+τ)
  have hErrorInt : Integrable (fun ω => (1+τ⁻¹)*(σ/M.nu)*err ω) μ := by
    exact hErrInt'.const_mul ((1+τ⁻¹)*(σ/M.nu))
  have hRhsInt : Integrable (fun ω => (1+τ)*parentEnergy ω+
      (1+τ⁻¹)*(σ/M.nu)*err ω) μ := hParentInt.add hErrorInt
  have hPoint : ∀ᵐ ω ∂μ,
      σ⁻¹ * vecDot e (matVecMul (coarseBlockMatrix (cubeSet Q)
        (Cutoff.coefficientCutoff M.nu N ω).toFun).upperLeft e) ≤
        (1+τ)*parentEnergy ω + (1+τ⁻¹)*(σ/M.nu)*err ω := by
    filter_upwards [ae_memBlockL2_bandLoad M n N σ e Q, hLocalVar, hCell,
      hApprox] with ω hload hlocal hcell happrox
    let d : Vec 2 → Vec 2 := fun x => localStreamApprox Q L S D ω x-(realize j ω x).toVec
    have hcorr : ∀ R ∈ descendantsAtScale Q q,
        ScalarVariation (openCubeSet R) (translatedCellCorrection C R ω) := hcell
    have hY : MemBlockL2 (openCubeSet Q) (tiledBandTrial M n N σ e C Q q ω) :=
      tiled_trial_memBlockL2 M n N σ e C Q q hq ω hload hcorr
    have hd : MemVectorL2 (openCubeSet Q) d := by
      have hH : MemHilbertVectorL2 (cubeSet Q) (fun x =>
          HilbertVec.ofVec (localStreamApprox Q L S D ω x)-realize j ω x) := happrox
      have hH' : MemHilbertVectorL2 (cubeSet Q) (fun x => HilbertVec.ofVec (d x)) := by
        have hfun : (fun x => HilbertVec.ofVec (d x)) = fun x =>
            HilbertVec.ofVec (localStreamApprox Q L S D ω x)-realize j ω x := by
          funext x
          dsimp [d]
        rw [hfun]
        exact hH
      have hv := (HilbertVec.continuousLinearEquivVec 2).toContinuousLinearMap.comp_memLp' hH'
      change MemLp d 2 (volume.restrict (openCubeSet Q))
      rw [← volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
      simpa only [Function.comp_apply, HilbertVec.continuousLinearEquivVec_apply,
        HilbertVec.toVec_ofVec] using! hv
    have hF := tiled_trial_bottom_error_admissible M n N σ e C Q q hq ω
      (localStreamApprox Q L S D ω) hlocal hcorr
    have htop := bottom_error_top_trial_le M N σ τ hσ hτ Q ω e
      (tiledBandTrial M n N σ e C Q q ω) d hY hd hF
    have havg := local_error_average_eq M n N σ e Q L S D ω happrox
    have hright :
        (1+τ)*volumeAverage (openCubeSet Q) (fun x => responseFrameEnergyDensity M.nu σ
          (Cutoff.cutoff N ω x 1 0) (tiledBandTrial M n N σ e C Q q ω x)) +
          (1+τ⁻¹)*(σ/M.nu)*volumeAverage (openCubeSet Q) (fun x => vecNormSq (d x)) ≤
        (1+τ)*parentEnergy ω+(1+τ⁻¹)*(σ/M.nu)*err ω := by
      rw [havg]
      rfl
    simpa [parentEnergy, err, Q, j, d, cutoffTrialEnergy] using htop.trans hright
  have hIntegral := integral_mono_ae
    (hTopInt.const_mul σ⁻¹)
    hRhsInt
    hPoint
  calc
    σ⁻¹ * (Homogenization.Book.Ch04.annealedBlockMatrixAtScale
        (Cutoff.coefficientCutoffLaw M N) k).upperLeft 0 0 =
        ∫ ω, σ⁻¹ * vecDot e (matVecMul (coarseBlockMatrix (cubeSet Q)
          (Cutoff.coefficientCutoff M.nu N ω).toFun).upperLeft e) ∂μ := by
      rw [integral_const_mul, integral_cutoff_unit_top_quadratic M N k e he]
    _ ≤ ∫ ω, (1+τ)*parentEnergy ω +
          (1+τ⁻¹)*(σ/M.nu)*err ω ∂μ := hIntegral
    _ = (1+τ) * (∫ ω, sourceEnergy ω ∂μ) +
          (1+τ⁻¹)*(σ/M.nu) * (∫ ω, err ω ∂μ) := by
      rw [integral_add hParentInt hErrorInt, integral_const_mul, integral_const_mul,
        hTiled.2]

end
end ASDExplicitGamma.Scalar
