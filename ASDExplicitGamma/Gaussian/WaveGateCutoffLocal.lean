module

public import ASDExplicitGamma.Gaussian.WaveGateLocalSupremum
public import ASDExplicitGamma.Gaussian.WaveGateEstimates
public import Algsuperdiff.Section3.Cutoff.LocalLimit

/-! The exact wave event is local on the genuine lower-infinite cutoff carrier. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization ASDExplicitGamma.Model Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff MeasureTheory
noncomputable section

/-- Every shell at or below m is measured in the same completed local lower
stream, with its genuine integral-local shell sigma-field. -/
theorem wave_gate_cutoff_coordinate_local (M : ABKModel 2) (m L : ℤ) (hL : L ≤ m)
    (U : Set (Vec 2)) :
    @Measurable (CutoffSample 2) (ShellField 2) (cutoffSampleLocalSigma M m U)
      (ShellField.lihLocalSigma U) (fun ω => ω.val L) := by
  obtain ⟨r,hr⟩ : ∃ r : ℕ, L = m-(r:ℤ) := by
    refine ⟨(m-L).toNat,?_⟩
    omega
  have hc := measurable_lowerShellLocal_coordinate m U r
  have hm : @Measurable (ShellSeq 2) (ShellField 2) (lowerShellLocalCompletion M m U)
      (ShellField.lihLocalSigma U) (fun ω => ω (m-(r:ℤ))) :=
    hc.mono (lowerShellLocalSigma_le_completion M m U) le_rfl
  have hs : @Measurable (CutoffSample 2) (ShellSeq 2) (cutoffSampleLocalSigma M m U)
      (lowerShellLocalCompletion M m U) Subtype.val := Measurable.of_comap_le le_rfl
  rw [hr]
  exact hm.comp hs

/-- The literal derivative size at one actual physical square is measurable
in the completed local cutoff information, with no covariance premise. -/
theorem wave_gate_cutoff_size_local (M : ABKModel 2) (m L : ℤ) (hL : L ≤ m)
    {U : Set (Vec 2)} (c : Vec 2) (s σ : ℝ) (hs : 0 < s) (hU : supMeanClosedSquare c s ⊆ U) :
    @Measurable (CutoffSample 2) ℝ (cutoffSampleLocalSigma M m U) inferInstance
      (fun ω => waveGateDerivativeSize c s σ (ω.val L)) :=
  (wave_gate_derivative_size_local_measurable c s σ hs hU).comp
    (wave_gate_cutoff_coordinate_local M m L hL U)

end
end ASDExplicitGamma.Gaussian
