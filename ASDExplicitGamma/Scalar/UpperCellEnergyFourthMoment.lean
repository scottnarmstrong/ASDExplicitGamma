module

public import ASDExplicitGamma.Scalar.UpperCellEnergyPotentialGaussian
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import ASDExplicitGamma.Scalar.UpperCellEnergyResetGaussianSquares

/-! Conversion of the squared-load L2 payment to the principal L4 cap. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- Squaring the L4 norm gives the L2 norm of the squared pointwise norm. -/
theorem upper_cell_fourth_moment_from_square
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) (f : Ω → E) (hf : AEStronglyMeasurable f μ)
    (hs : MemLp (fun ω => ‖f ω‖^2) 2 μ)
    (hb : lpNorm (fun ω => ‖f ω‖^2) 2 μ ≤ 4) :
    MemLp f 4 μ ∧ lpNorm f 4 μ ≤ 2 := by
  have hm := memLp_norm_rpow_iff (p := 4) (q := 2) hf (by norm_num) (by norm_num)
  norm_num only [ENNReal.toReal_ofNat,Real.rpow_two,show (4:ℝ≥0∞)/2=2 by
    rw [show (4:ℝ≥0∞)=2*2 by norm_num,ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)]] at hm
  have he := eLpNorm_norm_rpow (p := 2) (q := 2) f hf (by norm_num)
  norm_num only [Real.rpow_two,ENNReal.ofReal_ofNat,ENNReal.rpow_two,
    show (2:ℝ≥0∞)*2=4 by norm_num] at he
  have hn : lpNorm (fun ω => ‖f ω‖^2) 2 μ = (lpNorm f 4 μ)^2 := by
    simpa only [ENNReal.toReal_pow,toReal_eLpNorm] using congrArg ENNReal.toReal he
  refine ⟨hm.mp hs,?_⟩
  rw [hn] at hb
  nlinarith only [hb,lpNorm_nonneg (f := f) (p := 4) (μ := μ)]

end
end ASDExplicitGamma.Scalar
