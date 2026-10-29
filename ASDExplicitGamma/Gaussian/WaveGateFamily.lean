module

public import ASDExplicitGamma.Gaussian.WaveGateCutoffLocal

/-! The actual two-generation event family may have different elementary old/fresh labels. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization ASDExplicitGamma.Model Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff MeasureTheory
noncomputable section

/-- The source enlarged family: every elementary event retains its own fine
label, old buffered true frame and fresh shell at that label plus 40+Lambda. -/
def waveGateFamilyFailure (M : ABKModel 2) (Λ : ℤ) (η : ℝ)
    (j : WavePlanarElementaryIndex → ℤ) (c : WavePlanarElementaryIndex → Vec 2)
    (s : WavePlanarElementaryIndex → ℝ) : Set (CutoffSample 2) :=
  {ω | ∃ i, η*(3:ℝ)^(-(Λ:ℝ)/8) < waveGateDerivativeSize (c i) (s i)
    (Annealed.sigmaBar M (j i+40):ℝ) (ω.val (j i+40+Λ))}

/-- A heterogeneous family member has the same raw source rate and exact
union allowance, without replacing its true scalar by another member's frame. -/
theorem wave_gate_family_member_tail (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (j Λ : ℤ) (hLower : shellVarianceSum h M.gamma (j+40)/4 ≤ (Annealed.sigmaBar M (j+40):ℝ)^2)
    (hΛ : 1 ≤ Λ) (η : ℝ) (hη : 0 < η) (hg : M.gamma ≤ 1/64)
    (hm : M.gamma ≤ η^2*3^80/(12*waveBufferMean^2))
    (ht : M.gamma ≤ η^2*3^80/(60*waveBufferEll^2*(1200+(6+(11/5:ℝ)*40)/5)))
    (c : Vec 2) (s : ℝ) (hs : 0 < s) (hside : s ≤ (3:ℝ)^j) :
    (cutoffSampleLaw M).toMeasure.real {ω | η*(3:ℝ)^(-(Λ:ℝ)/8) <
      waveGateDerivativeSize c s (Annealed.sigmaBar M (j+40):ℝ) (ω.val (j+40+Λ))} ≤
      Real.exp (-(1200+(6+(11/5:ℝ)*40)/5)*(3:ℝ)^((3/2:ℝ)*(Λ:ℝ))) := by
  let E : Set (ShellField 2) := {F | η*(3:ℝ)^(-(Λ:ℝ)/8) <
    waveGateDerivativeSize c s (Annealed.sigmaBar M (j+40):ℝ) F}
  have hmap : (cutoffSampleLaw M).toMeasure.map (fun ω : CutoffSample 2 => ω.val (j+40+Λ)) =
      (ShellField.shellMarginalLaw M.P (j+40+Λ)).toMeasure := by
    calc
      _ = ((cutoffSampleLaw M).toMeasure.map (Subtype.val : CutoffSample 2 → ShellSeq 2)).map
          (fun F : ShellSeq 2 => F (j+40+Λ)) :=
        (Measure.map_map (ShellField.measurable_shellCoordinate _) measurable_subtype_coe).symm
      _ = _ := by rw [map_cutoffSampleLaw_val]; rfl
  have hle := Measure.le_map_apply (μ := (cutoffSampleLaw M).toMeasure)
    ((ShellField.measurable_shellCoordinate (j+40+Λ)).comp measurable_subtype_coe).aemeasurable E
  change (cutoffSampleLaw M).toMeasure ((fun ω : CutoffSample 2 => ω.val (j+40+Λ)) ⁻¹' E) ≤
    ((cutoffSampleLaw M).toMeasure.map (fun ω : CutoffSample 2 => ω.val (j+40+Λ))) E at hle
  rw [hmap] at hle
  have hr := ENNReal.toReal_mono (measure_ne_top _ E) hle
  exact hr.trans (wave_gate_elementary_tail M h hM j Λ hLower hΛ η hη hg hm ht c s hs hside)

/-- The actual extended family has the same rate-1200 tail even when its
parent and descendant events use different old and fresh shell labels. -/
theorem q3_wave_gate_family (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (t : WaveGateTuple) (Λ : ℤ) (hΛ : 1 ≤ Λ)
    (j : WavePlanarElementaryIndex → ℤ) (c : WavePlanarElementaryIndex → Vec 2)
    (s : WavePlanarElementaryIndex → ℝ) (hs : ∀ i, 0 < s i) (hside : ∀ i, s i ≤ (3:ℝ)^(j i))
    (hLower : ∀ i, shellVarianceSum h M.gamma (j i+40)/4 ≤ (Annealed.sigmaBar M (j i+40):ℝ)^2) :
    (cutoffSampleLaw M).toMeasure.real (waveGateFamilyFailure M Λ (waveGateEta t) j c s) ≤
      Real.exp (-1200*(3:ℝ)^((3/2:ℝ)*(Λ:ℝ))) := by
  obtain ⟨hm,ht,hg⟩ := wave_gate_tuple_margins t M.gamma hγ
  let E (i : WavePlanarElementaryIndex) : Set (CutoffSample 2) :=
    {ω | waveGateEta t*(3:ℝ)^(-(Λ:ℝ)/8) < waveGateDerivativeSize (c i) (s i)
      (Annealed.sigmaBar M (j i+40):ℝ) (ω.val (j i+40+Λ))}
  let z := (3:ℝ)^((3/2:ℝ)*(Λ:ℝ))
  let A := ((6+(11/5:ℝ)*40)/5)*z
  have hc : (Fintype.card WavePlanarElementaryIndex:ℝ) ≤ Real.exp A := by
    rw [wave_planar_elementary_card]
    exact wave_planar_union_cost Λ hΛ
  have hE (i : WavePlanarElementaryIndex) : (cutoffSampleLaw M).toMeasure.real (E i) ≤ Real.exp (-(A+1200*z)) := by
    have hh := wave_gate_family_member_tail M h hM (j i) Λ (hLower i) hΛ _ (wave_gate_eta_pos t)
      hg hm ht (c i) (s i) (hs i) (hside i)
    convert hh using 1
    congr 1
    dsimp only [A,z]
    ring
  have hh := wave_finite_union_tail (cutoffSampleLaw M).toMeasure E A (1200*z) hc hE
  simpa only [waveGateFamilyFailure,E,Set.iUnion_ofPred,z,neg_mul] using! hh

/-- The finite failure family is measurable on the original cutoff sample carrier. -/
theorem wave_gate_family_measurable (M : ABKModel 2) (Λ : ℤ) (η : ℝ)
    (j : WavePlanarElementaryIndex → ℤ) (c : WavePlanarElementaryIndex → Vec 2)
    (s : WavePlanarElementaryIndex → ℝ) (hs : ∀ i, 0 < s i) :
    MeasurableSet (waveGateFamilyFailure M Λ η j c s) := by
  have hm (i : WavePlanarElementaryIndex) : MeasurableSet {ω : CutoffSample 2 |
      η*(3:ℝ)^(-(Λ:ℝ)/8) < waveGateDerivativeSize (c i) (s i)
        (Annealed.sigmaBar M (j i+40):ℝ) (ω.val (j i+40+Λ))} := by
    have hf : Measurable (waveGateDerivativeSize (c i) (s i) (Annealed.sigmaBar M (j i+40):ℝ)) :=
      (wave_gate_derivative_size_local_measurable (c i) (s i) _ (hs i) (Set.Subset.refl _)).mono
        (ShellField.lihLocalSigma_le_borel _) le_rfl
    exact measurableSet_lt measurable_const
      (hf.comp ((ShellField.measurable_shellCoordinate _).comp measurable_subtype_coe))
  simpa only [waveGateFamilyFailure,Set.iUnion_ofPred] using MeasurableSet.iUnion hm

/-- The complete extended family is local below any common upper fresh label. -/
theorem wave_gate_family_local (M : ABKModel 2) (Λ m : ℤ) (η : ℝ)
    (j : WavePlanarElementaryIndex → ℤ) (hlabel : ∀ i, j i+40+Λ ≤ m)
    {U : Set (Vec 2)} (c : WavePlanarElementaryIndex → Vec 2) (s : WavePlanarElementaryIndex → ℝ)
    (hs : ∀ i, 0 < s i) (hU : ∀ i, supMeanClosedSquare (c i) (s i) ⊆ U) :
    MeasurableSet[cutoffSampleLocalSigma M m U] (waveGateFamilyFailure M Λ η j c s) := by
  let waveGateLocalInfo : MeasurableSpace (CutoffSample 2) := cutoffSampleLocalSigma M m U
  have hm (i : WavePlanarElementaryIndex) : MeasurableSet {ω : CutoffSample 2 |
      η*(3:ℝ)^(-(Λ:ℝ)/8) < waveGateDerivativeSize (c i) (s i)
        (Annealed.sigmaBar M (j i+40):ℝ) (ω.val (j i+40+Λ))} :=
    measurableSet_lt measurable_const (wave_gate_cutoff_size_local M m _ (hlabel i) (c i) (s i) _ (hs i) (hU i))
  simpa only [waveGateFamilyFailure,Set.iUnion_ofPred] using MeasurableSet.iUnion hm

end
end ASDExplicitGamma.Gaussian
