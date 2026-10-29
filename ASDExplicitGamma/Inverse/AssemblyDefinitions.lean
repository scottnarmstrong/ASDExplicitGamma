module

public import ASDExplicitGamma.Inverse.OrderBandBounds
public import ASDExplicitGamma.Inverse.AllOrderPlanarInterpolation
public import ASDExplicitGamma.Inverse.ShearedMatrix

/-! Literal positive error carriers for the all-order root assembly. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open scoped ENNReal Matrix.Norms.Elementwise

noncomputable section

/-- The deterministic source error clock at height `H` and Whitney layer `i`.
For the source range `H ≥ 377` and `i ≥ 1`, its exponent is the root-relative
offset `x_{i,H} = f_i + H - 38`. -/
def rootAssemblyClock (γ : ℝ) (H i : ℕ) : ℝ :=
  (3 : ℝ) ^ (2 * γ * (layerRelativeOffset H i : ℝ))

/-- The sensitivity prefactor from the source positive-energy comparison. -/
def rootAssemblySensitivity : ℝ :=
  Real.exp ((17444 / 10000 : ℝ) * (1 + resetAllOrderTau) *
    (10 * waveGateEta .allOrder))

theorem root_assembly_clock_pos (γ : ℝ) (H i : ℕ) :
    0 < rootAssemblyClock γ H i := by
  unfold rootAssemblyClock
  exact Real.rpow_pos_of_pos (by norm_num) _

theorem root_assembly_sensitivity_pos :
    0 < rootAssemblySensitivity := by
  unfold rootAssemblySensitivity
  exact Real.exp_pos _

end
end ASDExplicitGamma.Inverse
