module

public import ASDExplicitGamma.Gaussian.Q3H3Series
public import ASDExplicitGamma.Gaussian.Q3KernelCovariance

/-! # Parseval identifies the actual H³-series first-jet covariance -/

@[expose] public section

open MeasureTheory Homogenization Set
open scoped Topology RealInnerProductSpace

namespace ASDExplicitGamma.Gaussian

/-- Projecting the first jet to its value gives the continuous coefficient field. -/
noncomputable def q3H3RangeValue (a b c d β : ℝ) (L : {l : ℝ // 0 < l}) :
    Q3H3Range a b c d β L →L[ℝ] C(closedRectangle a b c d, ℝ) :=
  (ContinuousLinearMap.proj 0).comp (q3H3RangeC1 a b c d β L)

theorem q3H3RangeValue_factor (a b c d β : ℝ) (hab : a < b) (hcd : c < d)
    (L : {l : ℝ // 0 < l}) (u : WhiteNoise) (x : closedRectangle a b c d) :
    q3H3RangeValue a b c d β L (q3H3RangeFactor a b c d β L u) x =
      ⟪u, q3Section β L h3Zero x.1⟫ := by
  have hh := congrArg (fun j : C1Jet (closedRectangle a b c d) => j 0 x)
    (q3H3RangeC1_factor a b c d β hab hcd L u)
  exact hh

/-- The physical covariance is recovered without an assumed realization or trace identity. -/
theorem q3H3Directions_covariance {ι : Type*} [Countable ι] (a b c d β : ℝ)
    (hab : a < b) (hcd : c < d) (L : {l : ℝ // 0 < l}) (e : HilbertBasis ι ℝ WhiteNoise)
    (x y : closedRectangle a b c d) :
    (∑' n, q3H3RangeValue a b c d β L (q3H3Directions a b c d β L e n) x *
      q3H3RangeValue a b c d β L (q3H3Directions a b c d β L e n) y) =
      β ^ 2 * q3Cov ((x.1 0 - y.1 0) / L.1) * q3Cov ((x.1 1 - y.1 1) / L.1) := by
  let T := q3H3RangeValue a b c d β L
  rw [q3H3Directions, enumerated_tsum_apply
    (fun j => q3H3RangeFactor a b c d β L (e j))
    (fun v => T v x * T v y) (by simp only [map_zero, ContinuousMap.zero_apply, zero_mul])]
  dsimp only [T]
  simp_rw [q3H3RangeValue_factor a b c d β hab hcd L]
  have hh := e.tsum_inner_mul_inner (q3Section β L h3Zero x.1) (q3Section β L h3Zero y.1)
  calc
    _ = ∑' j, ⟪q3Section β L h3Zero x.1, e j⟫ * ⟪e j, q3Section β L h3Zero y.1⟫ := by
      apply tsum_congr
      intro j
      rw [real_inner_comm (e j) (q3Section β L h3Zero x.1)]
    _ = _ := hh.trans (q3Section_covariance β L x.1 y.1)

end ASDExplicitGamma.Gaussian
