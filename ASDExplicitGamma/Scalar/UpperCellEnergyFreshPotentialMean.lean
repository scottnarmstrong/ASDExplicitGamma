module

public import ASDExplicitGamma.Scalar.UpperCellEnergyOldFreshSigma
public import ASDExplicitGamma.Scalar.UpperCellEnergyPhysicalMeanJensen

/-! The literal physical potential mean uses only the full fresh shell family.
This retains the common fresh randomness with the derivative envelope. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Algsuperdiff.Section3 Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Probability.Stationary Algsuperdiff.Section3.Provider.Corrector
noncomputable section

/-- The entire finite-band spatial path is measurable from strictly later shells. -/
theorem upper_cell_band_path_fresh_measurable (n terminal : ℤ) :
    @Measurable _ _ (upperCellFreshSigma n) _
      (fun ω : Cutoff.CutoffSample 2 => shellSumValuePath n terminal ω.val) := by
  unfold shellSumValuePath
  exact Finset.measurable_sum _ (fun k hk =>
    ShellField.measurable_valuePath.comp
      (upper_cell_shell_fresh_measurable n k (Finset.mem_Ioc.mp hk).1))

/-- Averaging the actual corrector on its continuous-path carrier is measurable. -/
theorem upper_cell_potential_path_mean_measurable
    (M : ABKModel 2) (n terminal : ℤ) (c : ℝ) (e : Vec 2) (Q : TriadicCube 2) (i : Fin 2) :
    StronglyMeasurable (fun path : C(Vec 2, Mat 2) => cubeAverage Q
      (fun x => (shellSumCorrectorRepr M (c • e) n terminal (x +ᵥ path)).ofLp i)) := by
  have hm : StronglyMeasurable (fun path : C(Vec 2, Mat 2) =>
      (shellSumCorrectorRepr M (c • e) n terminal path).ofLp i) :=
    (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 2 => ℝ) i).continuous.comp_stronglyMeasurable
      (stronglyMeasurable_shellSumCorrectorRepr M (c • e) n terminal)
  unfold cubeAverage
  exact ((stronglyMeasurable_uncurry_realize hm).integral_prod_right'
    (ν := volume.restrict (cubeSet Q))).const_mul _

/-- The canonical physical potential mean is a fresh observable, pointwise
on the original cutoff carrier; no choice of a new representative is made. -/
theorem upper_cell_physical_potential_mean_fresh_measurable
    (M : ABKModel 2) (n terminal : ℤ) (c : ℝ) (e : Vec 2) (Q : TriadicCube 2) (i : Fin 2) :
    @Measurable _ _ (upperCellFreshSigma n) _
      (fun ω => upperCellPhysicalPotentialMean M n terminal c e Q ω i) := by
  have hm := (upper_cell_potential_path_mean_measurable M n terminal c e Q i).measurable.comp
    (upper_cell_band_path_fresh_measurable n terminal)
  convert hm using 1
  funext ω
  unfold upperCellPhysicalPotentialMean
  apply congrArg (cubeAverage Q)
  funext x
  change (shellSumCorrectorRepr M (c • e) n terminal
    (shellSumValuePath n terminal (x +ᵥ ω).val)).ofLp i = _
  rw [show shellSumValuePath n terminal (x +ᵥ ω).val = x +ᵥ shellSumValuePath n terminal ω.val from
    shellSumValuePath_translateSequence n terminal x ω.val]

end
end ASDExplicitGamma.Scalar
