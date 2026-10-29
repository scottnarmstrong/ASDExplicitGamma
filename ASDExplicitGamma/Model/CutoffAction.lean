module

public import Algsuperdiff.Section3.Cutoff.Symmetry
public import Algsuperdiff.Section3.Provider.Corrector.ShellSumLayerCarrier

@[expose] public section

open MeasureTheory Homogenization
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.Corrector
open scoped Matrix.Norms.Elementwise

namespace ASDExplicitGamma.Model

/-- Joint continuity of shell translation, including both derivative paths. -/
theorem continuous_shellTranslate_joint {d : ℕ} :
    Continuous (fun p : Vec d × ShellField d => ShellField.translate p.1 p.2) := by
  have hm : Continuous (ShellField.translateMap (d := d)) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun p : Vec d × Vec d => p.2 + p.1)
    exact continuous_snd.add continuous_fst
  have hcomp {E : Type} [TopologicalSpace E] [LocallyCompactPair (Vec d) E] :
      Continuous (fun p : Vec d × C(Vec d, E) => p.2.comp (ShellField.translateMap p.1)) :=
    continuous_snd.compCM (hm.comp continuous_fst)
  apply Continuous.subtype_mk
  change Continuous (fun p : Vec d × ShellField d =>
    ((p.2.1.1).comp (ShellField.translateMap p.1),
      ((p.2.1.2.1).comp (ShellField.translateMap p.1),
        (p.2.1.2.2).comp (ShellField.translateMap p.1))))
  have hv : Continuous (fun p : Vec d × ShellField d => p.2.1) :=
    continuous_subtype_val.comp continuous_snd
  exact ((hcomp (E := Mat d)).comp (continuous_fst.prodMk hv.fst)).prodMk
    (((hcomp (E := Vec d →L[ℝ] Mat d)).comp (continuous_fst.prodMk hv.snd.fst)).prodMk
      ((hcomp (E := Vec d →L[ℝ] (Vec d →L[ℝ] Mat d))).comp (continuous_fst.prodMk hv.snd.snd)))

/-- Real translations act on the literal convergent cutoff carrier. -/
noncomputable instance cutoffSampleAddAction (d : ℕ) : AddAction (Vec d) (Cutoff.CutoffSample d) where
  vadd := Cutoff.translateCutoffSample
  zero_vadd ω := by
    apply Subtype.ext
    funext k
    apply ShellField.ext
    intro x
    change ω.1 k (x + 0) = ω.1 k x
    rw [add_zero]
  add_vadd z w ω := by
    apply Subtype.ext
    funext k
    apply ShellField.ext
    intro x
    change ω.1 k (x + (z + w)) = ω.1 k ((x + z) + w)
    rw [add_assoc]

noncomputable instance cutoffSampleMeasurableVAdd (d : ℕ) :
    MeasurableVAdd₂ (Vec d) (Cutoff.CutoffSample d) where
  measurable_vadd := by
    apply Measurable.subtype_mk
    apply measurable_pi_iff.mpr
    intro k
    exact continuous_shellTranslate_joint.measurable.comp
      (measurable_fst.prodMk ((measurable_pi_apply k).comp
        (measurable_subtype_coe.comp measurable_snd)))

noncomputable instance cutoffSampleMeasurableConstVAdd (d : ℕ) :
    MeasurableConstVAdd (Vec d) (Cutoff.CutoffSample d) :=
  ⟨fun z => Cutoff.measurable_translateCutoffSample z⟩

noncomputable instance cutoffSampleVAddInvariantMeasure {d : ℕ} (M : ABKModel d) :
    VAddInvariantMeasure (Vec d) (Cutoff.CutoffSample d) (Cutoff.cutoffSampleLaw M).toMeasure where
  measure_preimage_vadd z s hs := by
    have h := congrArg (fun ν : Measure (Cutoff.CutoffSample d) => ν s)
      (Cutoff.map_translateCutoffSample_cutoffSampleLaw M z)
    rw [Measure.map_apply (Cutoff.measurable_translateCutoffSample z) hs] at h
    exact h

/-- The map to value-path sequences preserves the exact cutoff-sample law. -/
theorem measurePreserving_cutoffSeqPath {d : ℕ} (M : ABKModel d) :
    MeasurePreserving (fun ω : Cutoff.CutoffSample d => seqValuePath ω.1)
      (Cutoff.cutoffSampleLaw M).toMeasure (seqPathLaw M.P).toMeasure := by
  refine ⟨measurable_seqValuePath.comp measurable_subtype_coe, ?_⟩
  rw [seqPathLaw_toMeasure, ← Cutoff.map_cutoffSampleLaw_val M,
    Measure.map_map measurable_seqValuePath measurable_subtype_coe]
  rfl

theorem cutoffSeqPath_vadd {d : ℕ} (z : Vec d) (ω : Cutoff.CutoffSample d) :
    seqValuePath (z +ᵥ ω).1 = z +ᵥ seqValuePath ω.1 :=
  seqValuePath_translateSequence z ω.1

end ASDExplicitGamma.Model
