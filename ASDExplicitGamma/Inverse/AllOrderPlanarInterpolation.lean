module

public import ASDExplicitGamma.Inverse.AllOrderStoppedGeometry
public import ASDExplicitGamma.Inverse.PlanarGeometry

/-! All-order specialization of the actual q3 planar interpolation geometry. -/

@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open scoped ENNReal

/-- The q3 geometry theorem at the all-order entrance. This specializes
the actual stopped interpolation, including the active-gradient charge,
finite-energy midpoint map, and solenoidal zero-normal-trace flux, to the
gate and its protected native past. -/
noncomputable def reset_q3_planar_geometry
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (Q : TriadicCube 2) (p : ℝ) (_hp : 2 ≤ p)
    (hpast : ∀ n : ℤ,
      n ≤ Q.scale - 342 - 12 * orderBand p → nativeInductionState M h n) :=
  q3_planar_geometry M h hM hγ Q
    (heightEntrance (orderBand p) + 5) (by
      unfold heightEntrance
      omega)
    resetAllOrderTau (by
      norm_num [resetAllOrderTau, Numerics.Wave.allOrderTau])
    .allOrder (allOrderDensity : ℝ)
    (le_of_lt ((Real.exp_pos (-6000)).trans all_order_density_floor))
    all_order_density_small all_order_density_covers_raw
    (by
      intro n hn
      have hlabels : Q.scale -
          ((heightEntrance (orderBand p) + 5 : ℕ) : ℤ) + 40 =
          Q.scale - 342 - 12 * orderBand p := by
        unfold heightEntrance
        omega
      rw [hlabels] at hn
      exact hpast n hn)

end Inverse
