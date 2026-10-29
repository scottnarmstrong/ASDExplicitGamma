module

public import ASDExplicitGamma.Gaussian.GeneratorAlgebra
public import ASDExplicitGamma.Gaussian.ChildResponse
public import ASDExplicitGamma.Gaussian.BandFactor
public import ASDExplicitGamma.Native.HeatInitialDescendants
public import ASDExplicitGamma.Native.HeatShearMoment
public import ASDExplicitGamma.Inverse.BankHistoryPhysical
public import ASDExplicitGamma.Inverse.BankLocal
public import ASDExplicitGamma.Inverse.ClippedMatrixLocal
public import ASDExplicitGamma.Model.CutoffGaussian
public import ASDExplicitGamma.Gaussian.ModelHeatTrace
public import ASDExplicitGamma.Variational.TraceDefect
public import ASDExplicitGamma.Cold.NativeGraphTraceAverage
public import ASDExplicitGamma.Cold.SquareCellMean
public import ASDExplicitGamma.Native.HeatVHEATChild
public import ASDExplicitGamma.Statements.NativeInductionState
public import ASDExplicitGamma.Inverse.AnchorAdapter
public import ASDExplicitGamma.Native.HeatTrueFrameCooperativeCurve
public import ASDExplicitGamma.Native.HeatVHEATCarrierSourceTransport
public import ASDExplicitGamma.Native.HeatRemainderControlJointLaw
public import ASDExplicitGamma.Inverse.RawShellQ3Bracket
public import ASDExplicitGamma.Main.CubeFactor
public import ASDExplicitGamma.Inverse.PureFluxGeneratorActualQ3
public import ASDExplicitGamma.Inverse.PureFluxGeneratorDirectionBridge

/-! Young's cancellation for the gradient-square component of the actual
center/mixed/remainder split. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Gaussian ASDExplicitGamma.Main ASDExplicitGamma.Inverse
open Homogenization
open MeasureTheory
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3

/-- The summable scalar Young inequality, with the mixed term retained until
after summation. -/
theorem nativeHeat_summable_young_tsum {a b : ℕ → ℝ}
    (ha : Summable (fun j => (a j) ^ 2))
    (hb : Summable (fun j => (b j) ^ 2))
    (hab : Summable (fun j => a j * b j))
    (θ : ℝ) (hθ : 0 < θ) :
    -θ * (∑' j, (a j) ^ 2) + 2 * (∑' j, a j * b j) +
        (∑' j, (b j) ^ 2) ≤
      (1 + θ⁻¹) * (∑' j, (b j) ^ 2) := by
  let f : ℕ → ℝ := fun j => -θ * (a j) ^ 2 + (2 * (a j * b j) + (b j) ^ 2)
  let g : ℕ → ℝ := fun j => (1 + θ⁻¹) * (b j) ^ 2
  have hθroot : (Real.sqrt θ) ^ 2 = θ := Real.sq_sqrt hθ.le
  have hθrootpos : 0 < Real.sqrt θ := Real.sqrt_pos.mpr hθ
  have hYoung (j : ℕ) : f j ≤ g j := by
    have hsq : 0 ≤ (Real.sqrt θ * a j - b j / Real.sqrt θ) ^ 2 := sq_nonneg _
    have hid : (Real.sqrt θ * a j - b j / Real.sqrt θ) ^ 2 =
        θ * (a j) ^ 2 - 2 * a j * b j + θ⁻¹ * (b j) ^ 2 := by
      calc
        _ = (Real.sqrt θ) ^ 2 * (a j) ^ 2 -
              2 * a j * b j + (b j) ^ 2 / (Real.sqrt θ) ^ 2 := by
          field_simp [ne_of_gt hθrootpos]
          ring
        _ = θ * (a j) ^ 2 - 2 * a j * b j +
              θ⁻¹ * (b j) ^ 2 := by
          rw [hθroot, div_eq_mul_inv]
          ring
    dsimp [f, g]
    nlinarith only [hsq, hid]
  have hF : Summable f := by
    have hsum : Summable (fun j => -θ * (a j) ^ 2 +
        (2 * (a j * b j) + (b j) ^ 2)) :=
      (ha.mul_left (-θ)).add ((hab.mul_left 2).add hb)
    simpa only [f] using hsum
  have hG : Summable g := by
    change Summable (fun j => (1 + θ⁻¹) * (b j) ^ 2)
    exact hb.mul_left _
  have hsum : (∑' j, f j) ≤ ∑' j, g j := hF.tsum_le_tsum hYoung hG
  have hsumF :
      (∑' j, f j) = -θ * (∑' j, (a j) ^ 2) +
        2 * (∑' j, a j * b j) + (∑' j, (b j) ^ 2) := by
    simp only [f]
    have hleft : Summable (fun j => -θ * (a j) ^ 2) := ha.mul_left _
    have hmid : Summable (fun j => 2 * (a j * b j)) := hab.mul_left _
    calc
      _ = (∑' j, -θ * (a j) ^ 2) +
            ((∑' j, 2 * (a j * b j)) + ∑' j, (b j) ^ 2) := by
          rw [hleft.tsum_add (hmid.add hb), hmid.tsum_add hb]
      _ = _ := by rw [tsum_mul_left, tsum_mul_left]; ring
  have hsumG :
      (∑' j, g j) = (1 + θ⁻¹) * (∑' j, (b j) ^ 2) := by
    change (∑' j, (1 + θ⁻¹) * (b j) ^ 2) = _
    exact tsum_mul_left
  rw [hsumF, hsumG] at hsum
  exact hsum

end ASDExplicitGamma.Native
