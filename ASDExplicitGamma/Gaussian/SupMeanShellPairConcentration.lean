module

public import ASDExplicitGamma.Gaussian.SupMeanShellUnitSupremum
public import ASDExplicitGamma.Gaussian.SupMeanShellPairKernel

/-! Sharp actual-law concentration for the combined physical derivative size. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization ASDExplicitGamma.Model Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3 MeasureTheory
noncomputable section

/-- The exact physical combined tensor size, with arbitrary deterministic
nonnegative weights, has sharp concentration under the frozen shell law.
Only the source Gaussian hypothesis remains; no concentration/variance input. -/
theorem supMean_shell_pair_tail (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (k : ℤ) (c : Vec 2) (s : ℝ) (hs : 0 < s)
    (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (t : ℝ) (ht : 0 ≤ t) :
    let F := fun j => a*‖supMeanShellSquareTensor Q3SpatialJet.first c s j‖+
      b*‖supMeanShellSquareTensor (fun i : Fin 2 × Fin 2 => .second i.1 i.2) c s j‖
    let C := a*Real.sqrt (waveEll1^2*((supMeanShellKernelAmplitude M h k)^2/((3:ℝ)^k)^2))+
      b*Real.sqrt (waveEll2^2*((supMeanShellKernelAmplitude M h k)^2/((3:ℝ)^k)^4))
    (ShellField.shellMarginalLaw M.P k).toMeasure.real {j | t ≤ F j-
      ∫ z, F z ∂(ShellField.shellMarginalLaw M.P k).toMeasure} ≤ Real.exp (-t^2/(2*C^2)) := by
  intro F C
  let hSquareNonempty : Nonempty (supMeanClosedSquare c s) :=
    ⟨⟨c,supMean_center_mem_closed_square c s hs.le⟩⟩
  have hAmp := supMean_shell_kernel_amplitude_pos M h hM k
  have hEll : 0 < waveEll1 := by norm_num [waveEll1,waveR1]
  have hC : 0 < C := by dsimp only [C]; positivity
  exact supMean_compact_pair_tail (ShellField.shellMarginalLaw M.P k).toMeasure
    (supMeanShellSquareTensor Q3SpatialJet.first c s)
    (supMeanShellSquareTensor (fun i : Fin 2 × Fin 2 => .second i.1 i.2) c s)
    a b ha.le hb (supMean_shell_first_supremum_mean M h hM k c s hs).1
    (supMean_shell_second_supremum_mean M h hM k c s hs).1
    (supMean_shell_pair_gaussian c s M h hM k a b) C t hC ht
    (supMean_shell_pair_projection_variance c s M h hM k a b ha.le hb)

end
end ASDExplicitGamma.Gaussian
