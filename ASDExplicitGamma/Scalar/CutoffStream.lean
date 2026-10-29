module

public import ASDExplicitGamma.Model.CutoffForcingIdentification
public import ASDExplicitGamma.Model.CutoffAction
public import ASDExplicitGamma.Scalar.DualAdmissibility
public import Algsuperdiff.Section3.Provider.Corrector.ShellSumCorrectorLimit
public import Algsuperdiff.Section3.Provider.Corrector.ShellSumConsumerTransport
public import Algsuperdiff.Section3.Provider.Corrector.SolenoidalApproximationEps

/-! Stationary approximate streams for the finite shell band. -/
@[expose] public section

open MeasureTheory Homogenization
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Corrector
open Algsuperdiff.Frozen.Assumptions

namespace ASDExplicitGamma.Scalar

/-- The actual shell-band corrected flux, transported to the full cutoff
sample carrier. This is the divergence-free bottom field used by the trial. -/
noncomputable def cutoffBandFlux (M : ABKModel 2) (n m : ℤ) (c : ℝ) (e : Vec 2)
    (ω : CutoffSample 2) : HilbertVec 2 :=
  shellSumFlux M (c • e) n m (shellSumValuePath n m ω.val)

/-- The transported band flux is strongly measurable on the cutoff carrier. -/
theorem stronglyMeasurable_cutoffBandFlux
    (M : ABKModel 2) (n m : ℤ) (c : ℝ) (e : Vec 2) :
    StronglyMeasurable (cutoffBandFlux M n m c e) := by
  unfold cutoffBandFlux
  exact (stronglyMeasurable_shellSumFlux M (c • e) n m).comp_measurable
    (measurePreserving_shellSumValuePath_cutoffSample M n m).measurable

/-- The transported band flux is square integrable on the cutoff carrier. -/
theorem memLp_two_cutoffBandFlux
    (M : ABKModel 2) (n m : ℤ) (c : ℝ) (e : Vec 2) :
    MemLp (cutoffBandFlux M n m c e) 2 (Cutoff.cutoffSampleLaw M).toMeasure := by
  unfold cutoffBandFlux
  exact (memLp_two_shellSumFlux M (c • e) n m).comp_measurePreserving
    (measurePreserving_shellSumValuePath_cutoffSample M n m)

private theorem shellSumValuePath_cutoff_vadd (n m : ℤ) (z : Vec 2)
    (ω : CutoffSample 2) :
    shellSumValuePath n m (z +ᵥ ω).val = z +ᵥ shellSumValuePath n m ω.val := by
  change shellSumValuePath n m (ShellField.translateSequence z ω.val) = _
  exact shellSumValuePath_translateSequence n m z ω.val

/-- Spatial realization of the cutoff-band flux agrees with the same shell
functional evaluated at the translated sample. -/
theorem realize_cutoffBandFlux_eq_shellSumFlux_translate
    (M : ABKModel 2) (n m : ℤ) (c : ℝ) (e x : Vec 2)
    (ω : CutoffSample 2) :
    realize (cutoffBandFlux M n m c e) ω x =
      shellSumFlux M (c • e) n m (shellSumValuePath n m (x +ᵥ ω).val) := by
  rw [realize_apply]
  rfl

/-- The exact finite-band solenoidal flux is covariant under spatial shifts of
the cutoff sample. -/
theorem realize_cutoffBandFlux_shift_sample
    (M : ABKModel 2) (n m : ℤ) (c : ℝ) (e z x : Vec 2)
    (ω : CutoffSample 2) :
    realize (cutoffBandFlux M n m c e) (z +ᵥ ω) x =
      realize (cutoffBandFlux M n m c e) ω (x + z) := by
  rw [realize_cutoffBandFlux_eq_shellSumFlux_translate,
    realize_cutoffBandFlux_eq_shellSumFlux_translate]
  congr 1
  rw [(add_vadd x z ω).symm]

/-- Pull a stationary approximate stream for the finite shell increment back to
the full cutoff-sample carrier. -/
theorem exists_cutoff_band_stream
    (M : ABKModel 2) (n m : ℤ) (c : ℝ) (e : Vec 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : CutoffSample 2 → (Fin 2 → HilbertVec 2),
      ∃ D : CutoffSample 2 → HilbertVec 2,
        StronglyMeasurable S ∧
        MemLp S 2 (Cutoff.cutoffSampleLaw M).toMeasure ∧
        (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure, ∀ i k : Fin 2,
          ContDiff ℝ (⊤ : ℕ∞) (streamRealization S ω i k)) ∧
        (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure, ∀ i k : Fin 2,
          streamRealization S ω k i = -streamRealization S ω i k) ∧
        (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure, ∀ x : Vec 2,
          streamDivergence (streamRealization S ω) x =
            (realize D ω x).toVec) ∧
        StronglyMeasurable D ∧
        MemLp D 2 (Cutoff.cutoffSampleLaw M).toMeasure ∧
        ∫ ω, ‖D ω - shellSumFlux M (c • e) n m
          (shellSumValuePath n m ω.val)‖ ^ 2
          ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤ ε := by
  obtain ⟨S₀, D₀, hS₀m, hS₀, hsm, hanti, hdiv, hD₀m, hD₀, herr⟩ :=
    exists_shellSumStream M (c • e) n m hε
  let path (ω : CutoffSample 2) := shellSumValuePath n m ω.val
  let S : CutoffSample 2 → (Fin 2 → HilbertVec 2) := fun ω => S₀ (path ω)
  let D : CutoffSample 2 → HilbertVec 2 := fun ω => D₀ (path ω)
  have hstream (ω : CutoffSample 2) :
      streamRealization S ω = streamRealization S₀ (path ω) := by
    funext i k x
    rw [streamRealization_apply, streamRealization_apply, realize_apply, realize_apply]
    change S₀ (shellSumValuePath n m (x +ᵥ ω).val) k i =
      S₀ (x +ᵥ path ω) k i
    rw [shellSumValuePath_cutoff_vadd]
  have hrealD (ω : CutoffSample 2) (x : Vec 2) :
      realize D ω x = realize D₀ (path ω) x := by
    rw [realize_apply, realize_apply]
    change D₀ (shellSumValuePath n m (x +ᵥ ω).val) = D₀ (x +ᵥ path ω)
    rw [shellSumValuePath_cutoff_vadd]
  have hmp := measurePreserving_shellSumValuePath_cutoffSample M n m
  have hSm : StronglyMeasurable S := by
    exact hS₀m.comp_measurable hmp.measurable
  have hS : MemLp S 2 (Cutoff.cutoffSampleLaw M).toMeasure := by
    exact hS₀.comp_measurePreserving hmp
  have hDm : StronglyMeasurable D := by
    exact hD₀m.comp_measurable hmp.measurable
  have hD : MemLp D 2 (Cutoff.cutoffSampleLaw M).toMeasure := by
    exact hD₀.comp_measurePreserving hmp
  have hsm' : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure, ∀ i k : Fin 2,
      ContDiff ℝ (⊤ : ℕ∞) (streamRealization S ω i k) := by
    filter_upwards [hmp.quasiMeasurePreserving.ae hsm] with ω hω
    intro i k
    rw [hstream]
    exact hω i k
  have hanti' : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure, ∀ i k : Fin 2,
      streamRealization S ω k i = -streamRealization S ω i k := by
    filter_upwards [hmp.quasiMeasurePreserving.ae hanti] with ω hω
    intro i k
    rw [hstream]
    exact hω i k
  have hdiv' : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure, ∀ x : Vec 2,
      streamDivergence (streamRealization S ω) x = (realize D ω x).toVec := by
    filter_upwards [hmp.quasiMeasurePreserving.ae hdiv] with ω hω
    intro x
    rw [hstream, hrealD]
    exact hω x
  have herr' : ∫ ω, ‖D ω - shellSumFlux M (c • e) n m (path ω)‖ ^ 2
      ∂(Cutoff.cutoffSampleLaw M).toMeasure =
      ∫ f, ‖D₀ f - shellSumFlux M (c • e) n m f‖ ^ 2
        ∂(shellSumValuePathLaw M.P n m).toMeasure := by
    have hdiff : AEMeasurable (fun f => D₀ f - shellSumFlux M (c • e) n m f)
        (shellSumValuePathLaw M.P n m).toMeasure :=
      (hD₀m.sub (stronglyMeasurable_shellSumFlux M (c • e) n m)).aemeasurable
    have hG : AEStronglyMeasurable
        (fun f => ‖D₀ f - shellSumFlux M (c • e) n m f‖ ^ 2)
        (shellSumValuePathLaw M.P n m).toMeasure := by
      exact ((continuous_norm.pow 2).measurable.comp_aemeasurable hdiff).aestronglyMeasurable
    exact integral_cutoffSample_comp_shellSumValuePath M n m
      (G := fun f => ‖D₀ f - shellSumFlux M (c • e) n m f‖ ^ 2)
      hG
  refine ⟨S, D, hSm, hS, hsm', hanti', hdiv', hDm, hD, ?_⟩
  simpa only [D, path] using herr'.trans_le herr

/-- The localized stationary stream has an actual L² representative on the
parent, for any fixed approximate stream data. -/
theorem ae_memVectorL2_localStreamApprox
    (M : ABKModel 2) (n m : ℤ) (c : ℝ) (e : Vec 2)
    (Q : TriadicCube 2) (L : ℕ)
    (S : CutoffSample 2 → (Fin 2 → HilbertVec 2))
    (D : CutoffSample 2 → HilbertVec 2)
    (hSm : StronglyMeasurable S)
    (hS : MemLp S 2 (Cutoff.cutoffSampleLaw M).toMeasure)
    (hDm : StronglyMeasurable D)
    (hD : MemLp D 2 (Cutoff.cutoffSampleLaw M).toMeasure) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      MemVectorL2 (openCubeSet Q) (localStreamApprox Q L S D ω) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let path (ω : CutoffSample 2) := shellSumValuePath n m ω.val
  let j (ω : CutoffSample 2) := shellSumFlux M (c • e) n m (path ω)
  have hjm : StronglyMeasurable j := by
    exact (stronglyMeasurable_shellSumFlux M (c • e) n m).comp_measurable
      (measurePreserving_shellSumValuePath_cutoffSample M n m).measurable
  have hj : MemLp j 2 μ := by
    exact (memLp_two_shellSumFlux M (c • e) n m).comp_measurePreserving
      (measurePreserving_shellSumValuePath_cutoffSample M n m)
  have happrox := ae_memLp_localStreamApprox_sub_of_approximateStream
    (μ := μ) Q L hSm hS hDm hD hjm hj
  have hrealize := ae_memLp_two_realize (μ := μ) (volume_cubeSet_lt_top Q).ne hjm hj
  filter_upwards [happrox, hrealize] with ω herrω hrealω
  have hlocalH : MemLp
      (fun x => HilbertVec.ofVec (localStreamApprox Q L S D ω x)) 2
      (volume.restrict (cubeSet Q)) := by
    have hsum : (fun x => HilbertVec.ofVec (localStreamApprox Q L S D ω x)) =
        (fun x => HilbertVec.ofVec (localStreamApprox Q L S D ω x) - realize j ω x) +
          fun x => realize j ω x := by
      funext x
      exact (sub_add_cancel (HilbertVec.ofVec (localStreamApprox Q L S D ω x))
        (realize j ω x)).symm
    rw [hsum]
    exact herrω.add hrealω
  have hlocal : MemVectorL2 (cubeSet Q) (localStreamApprox Q L S D ω) := by
    change MemLp (localStreamApprox Q L S D ω) 2 (volume.restrict (cubeSet Q))
    simpa only [Function.comp_apply, HilbertVec.continuousLinearEquivVec_apply,
      HilbertVec.toVec_ofVec] using!
      (HilbertVec.continuousLinearEquivVec 2).toContinuousLinearMap.comp_memLp' hlocalH
  change MemLp (localStreamApprox Q L S D ω) 2 (volume.restrict (openCubeSet Q))
  rw [← volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
  exact hlocal

end ASDExplicitGamma.Scalar
