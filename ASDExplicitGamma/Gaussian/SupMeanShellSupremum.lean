module

public import ASDExplicitGamma.Gaussian.SupMeanDyadicSupremum
public import ASDExplicitGamma.Gaussian.SupMeanShellTensorFields
public import ASDExplicitGamma.Gaussian.SupMeanShellMeanIncrement
public import ASDExplicitGamma.Gaussian.SupMeanShellIncrementConcentration

/-! Actual-law tensor supremum means on the physical square, with exact covariance scaling. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization ASDExplicitGamma.Model Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3 MeasureTheory
noncomputable section

/-- The actual stored tensor restricted to the actual compact physical square. -/
def supMeanShellSquareTensor {ι : Type} [Fintype ι] (o : ι → Q3SpatialJet)
    (c : Vec 2) (s : ℝ) (j : ShellField 2) : C(supMeanClosedSquare c s,EuclideanSpace ℝ ι) :=
  ⟨fun x => supMeanShellTensor o x.val j,
    (supMean_shell_tensor_spatial_continuous o j).comp continuous_subtype_val⟩

/-- GA-SUP-MEAN for the actual first stored tensor, in physical shell units.
Every supremum-integrability and increment-law input is proved internally. -/
theorem supMean_shell_first_supremum_mean (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (k : ℤ) (c : Vec 2) (s : ℝ) (hs : 0 < s) :
    Integrable (fun j => ‖supMeanShellSquareTensor Q3SpatialJet.first c s j‖)
      (ShellField.shellMarginalLaw M.P k).toMeasure ∧
    (∫ j, ‖supMeanShellSquareTensor Q3SpatialJet.first c s j‖
      ∂(ShellField.shellMarginalLaw M.P k).toMeasure) ≤
        Real.sqrt (waveTau1*((h^2*(3:ℝ)^(2*M.gamma*(k:ℝ)))/((3:ℝ)^k)^2))+
          (s*Real.sqrt ((h^2*(3:ℝ)^(2*M.gamma*(k:ℝ)))/((3:ℝ)^k)^4))*
            (Real.sqrt waveTau2/2+2*Real.sqrt (Real.log 2)*waveEll2) := by
  have hT : 0 ≤ waveTau2 := by norm_num [waveTau2, waveMu2, waveR1, waveR2]
  have hV : 0 < (h^2*(3:ℝ)^(2*M.gamma*(k:ℝ)))/((3:ℝ)^k)^4 := by
    have hh := hM.1
    positivity
  have hA : 0 < waveEll2 := by unfold waveEll2 waveR2 waveR1; positivity
  have hbase : (∫ j, ‖supMeanShellTensor Q3SpatialJet.first c j‖
      ∂(ShellField.shellMarginalLaw M.P k).toMeasure) ≤
        Real.sqrt (waveTau1*((h^2*(3:ℝ)^(2*M.gamma*(k:ℝ)))/((3:ℝ)^k)^2)) := by
    have hh := supMean_shell_first_tensor_mean M h hM k c
    convert hh using 1
    congr 1
    simp only [div_eq_mul_inv, inv_pow]
    ring_nf
  have hmean (x y : Vec 2) : (∫ j, ‖supMeanShellTensor Q3SpatialJet.first y j-
      supMeanShellTensor Q3SpatialJet.first x j‖ ∂(ShellField.shellMarginalLaw M.P k).toMeasure) ≤
        Real.sqrt ((waveTau2/2)*((h^2*(3:ℝ)^(2*M.gamma*(k:ℝ)))/((3:ℝ)^k)^4)*((y-x) 0^2+(y-x) 1^2)) := by
    simpa only [supMeanShellTensor, supMeanTensorNorm] using! supMean_shell_first_mean_increment M h hM k x y
  have hh := supMean_gaussian_square_supmean (ShellField.shellMarginalLaw M.P k).toMeasure c s hs
    (fun j x => supMeanShellTensor Q3SpatialJet.first x j)
    (fun j => supMean_shell_tensor_spatial_continuous Q3SpatialJet.first j)
    (fun x => supMean_shell_tensor_integrable M h hM k Q3SpatialJet.first x)
    (fun x => (supMean_shell_tensor_sample_continuous Q3SpatialJet.first x).measurable)
    _ waveTau2 _ waveEll2 hT hV hA hbase hmean (by
      intro x y lam _
      simpa only [supMean_shell_tensor_increment_norm] using! supMean_shell_first_increment_mgf M h hM k x y lam)
  exact hh

/-- GA-SUP-MEAN for the actual stored Hessian, in physical shell units.
The third weak kernel supplies the exact source tau_3 and ell_3 payments. -/
theorem supMean_shell_second_supremum_mean (M : ABKModel 2) (h : ℝ)
    (hM : PlanarQ3Gaussian M h) (k : ℤ) (c : Vec 2) (s : ℝ) (hs : 0 < s) :
    Integrable (fun j => ‖supMeanShellSquareTensor (fun i : Fin 2 × Fin 2 => .second i.1 i.2) c s j‖)
      (ShellField.shellMarginalLaw M.P k).toMeasure ∧
    (∫ j, ‖supMeanShellSquareTensor (fun i : Fin 2 × Fin 2 => .second i.1 i.2) c s j‖
      ∂(ShellField.shellMarginalLaw M.P k).toMeasure) ≤
        Real.sqrt (waveTau2*((h^2*(3:ℝ)^(2*M.gamma*(k:ℝ)))/((3:ℝ)^k)^4))+
          (s*Real.sqrt ((h^2*(3:ℝ)^(2*M.gamma*(k:ℝ)))/((3:ℝ)^k)^6))*
            (Real.sqrt waveTau3/2+2*Real.sqrt (Real.log 2)*waveEll3) := by
  let o : Fin 2 × Fin 2 → Q3SpatialJet := fun i => .second i.1 i.2
  have hT : 0 ≤ waveTau3 := by norm_num [waveTau3, waveMu3, waveR1, waveR2, waveR3]
  have hV : 0 < (h^2*(3:ℝ)^(2*M.gamma*(k:ℝ)))/((3:ℝ)^k)^6 := by
    have hh := hM.1
    positivity
  have hA : 0 < waveEll3 := by unfold waveEll3 waveMu3 waveR1 waveR2 waveR3; positivity
  have hbase : (∫ j, ‖supMeanShellTensor o c j‖
      ∂(ShellField.shellMarginalLaw M.P k).toMeasure) ≤
        Real.sqrt (waveTau2*((h^2*(3:ℝ)^(2*M.gamma*(k:ℝ)))/((3:ℝ)^k)^4)) := by
    have hh := supMean_shell_second_tensor_mean M h hM k c
    convert hh using 1
    congr 1
    ring_nf
  have hmean (x y : Vec 2) : (∫ j, ‖supMeanShellTensor o y j-supMeanShellTensor o x j‖
      ∂(ShellField.shellMarginalLaw M.P k).toMeasure) ≤
        Real.sqrt ((waveTau3/2)*((h^2*(3:ℝ)^(2*M.gamma*(k:ℝ)))/((3:ℝ)^k)^6)*((y-x) 0^2+(y-x) 1^2)) := by
    simpa only [o, supMeanShellTensor, supMeanTensorNorm] using! supMean_shell_second_mean_increment M h hM k x y
  have hh := supMean_gaussian_square_supmean (ShellField.shellMarginalLaw M.P k).toMeasure c s hs
    (fun j x => supMeanShellTensor o x j)
    (fun j => supMean_shell_tensor_spatial_continuous o j)
    (fun x => supMean_shell_tensor_integrable M h hM k o x)
    (fun x => (supMean_shell_tensor_sample_continuous o x).measurable)
    _ waveTau3 _ waveEll3 hT hV hA hbase hmean (by
      intro x y lam _
      simpa only [o, supMean_shell_tensor_increment_norm] using! supMean_shell_second_increment_mgf M h hM k x y lam)
  exact hh

end
end ASDExplicitGamma.Gaussian
