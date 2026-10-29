module

public import ASDExplicitGamma.Inverse.StoppedElementaryHistory
public import ASDExplicitGamma.Inverse.StoppedPhysicalContainment
public import ASDExplicitGamma.Inverse.StoppedMarkedField
public import ASDExplicitGamma.Gaussian.WaveGateFamily

/-! The source marked field on the genuine q3 cutoff sample space. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
noncomputable section

/-- Literal parent-and-two-generation marks on every physical buffered block. -/
def q3PlanarMarks (M : ABKModel 2) (j : ℤ) (τ η : ℝ) : PlanarMarks (Cutoff.CutoffSample 2) where
  localMark x := elementaryHistoryFailure M τ (elementaryCube j x)
  positiveMark n x := waveGateFamilyFailure M (n+1) η
    (fun i => (elementaryCube j x i).scale)
    (fun i => cubeCenter (elementaryCube j x i))
    (fun i => cubeScaleFactor (elementaryCube j x i))

theorem q3_local_mark_measurable (M : ABKModel 2) (j : ℤ) (τ η : ℝ) (x : BlockSite) :
    MeasurableSet ((q3PlanarMarks M j τ η).localMark x) :=
  elementary_history_failure_measurable M τ _

theorem q3_positive_mark_measurable (M : ABKModel 2) (j : ℤ) (τ η : ℝ)
    (n : ℕ) (x : BlockSite) :
    MeasurableSet ((q3PlanarMarks M j τ η).positiveMark n x) := by
  apply wave_gate_family_measurable
  intro i
  exact zpow_pos (by norm_num) _

/-- The old raw marks retain exactly the source E_b*pi_b union budget. -/
theorem q3_local_mark_probability (M : ABKModel 2) (hg : M.gamma ≤ gammaZero)
    (j : ℤ) (τ η : ℝ) (hτ : 0 < τ) (x : BlockSite)
    (hcap : ∀ i, buffer40History M ((elementaryCube j x i).scale+40) ≤
      ENNReal.ofReal (61/10*theta M)) :
    (Cutoff.cutoffSampleLaw M).toMeasure.real ((q3PlanarMarks M j τ η).localMark x) ≤
      (364*3^80:ℝ)*(3*(61/10:ℝ)/τ)^12 :=
  elementary_history_failure_probability M hg τ hτ _ hcap

/-- All descendant positive marks are measured at their own true old frame;
the common parent cutoff is used only to bound the observation sigma-field. -/
theorem q3_positive_mark_probability (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (j : ℤ) (τ : ℝ) (t : WaveGateTuple) (n : ℕ) (x : BlockSite)
    (hlower : ∀ i, shellVarianceSum h M.gamma ((elementaryCube j x i).scale+40)/4 ≤
      (Annealed.sigmaBar M ((elementaryCube j x i).scale+40):ℝ)^2) :
    (Cutoff.cutoffSampleLaw M).toMeasure.real
      ((q3PlanarMarks M j τ (waveGateEta t)).positiveMark n x) ≤
      Real.exp (-1200*(3:ℝ)^((3/2:ℝ)*((n:ℝ)+1))) := by
  have hh := q3_wave_gate_family M h hM hg t (n+1) (by omega)
    (fun i => (elementaryCube j x i).scale)
    (fun i => cubeCenter (elementaryCube j x i))
    (fun i => cubeScaleFactor (elementaryCube j x i))
    (fun _ => zpow_pos (by norm_num) _) (fun _ => le_rfl) hlower
  simpa only [q3PlanarMarks,Int.cast_add,Int.cast_natCast,Int.cast_one] using! hh

end
end ASDExplicitGamma.Inverse
