module

public import ASDExplicitGamma.Gaussian.CameronMartinFactor
public import ASDExplicitGamma.Gaussian.H3SeriesCompletion
public import ASDExplicitGamma.Gaussian.RectangleClosure

/-! # The genuine covariance Hilbert carrier of the centered q3 field -/

@[expose] public section

open MeasureTheory Homogenization Set
open scoped RealInnerProductSpace Topology

namespace ASDExplicitGamma.Gaussian

section
variable (a b c d β : ℝ) (L : {l : ℝ // 0 < l}) (x₀ : closedRectangle a b c d)

noncomputable def q3RemainderH3Factor : WhiteNoise →L[ℝ] h3Space (openRectangle a b c d) :=
  (q3H3RemainderMap a b c d β L x₀).comp (q3H3RangeFactor a b c d β L)

noncomputable def q3RemainderValueFactor : WhiteNoise →L[ℝ] C(closedRectangle a b c d, ℝ) :=
  (centeringMap x₀).comp ((q3H3RangeValue a b c d β L).comp (q3H3RangeFactor a b c d β L))

/-- The physical remainder and the ordinary weak H³ factor have exactly the same null
white-noise directions. -/
theorem q3RemainderFactor_kernel (hab : a < b) (hcd : c < d) (u : WhiteNoise) :
    q3RemainderH3Factor a b c d β L x₀ u = 0 ↔
      q3RemainderValueFactor a b c d β L x₀ u = 0 := by
  let U := openRectangle a b c d
  let z := q3H3RangeFactor a b c d β L u
  let j := q3C1RemainderMap a b c d β L x₀ z
  have hae := q3H3RemainderMap_value_ae a b c d β hab hcd L x₀ z
  have hval (x : closedRectangle a b c d) : c1JetValue j x.1 = j 0 x := by
    simp only [c1JetValue, dite_eq_left x.2]
  have hj : j 0 = q3RemainderValueFactor a b c d β L x₀ u := rfl
  constructor
  · intro hu
    have hzero : h3Value U (q3H3RemainderMap a b c d β L x₀ z) = 0 := by
      change h3Value U (q3RemainderH3Factor a b c d β L x₀ u) = 0
      rw [hu, map_zero]
    rw [hzero] at hae
    have hzeroae : c1JetValue j =ᵐ[volume.restrict U] 0 := by
      filter_upwards [hae, (Lp.coeFn_zero ℝ 2 (volume.restrict U))] with x hx hz
      exact hx.symm.trans hz
    rw [← hj]
    exact rectangle_value_eq_zero a b c d hab hcd (j 0) (c1JetValue j) hval hzeroae
  · intro hu
    apply h3Value_injective (openRectangle_isOpen a b c d)
    rw [map_zero]
    apply Lp.ext
    filter_upwards [hae, (Lp.coeFn_zero ℝ 2 (volume.restrict U)),
      ae_restrict_mem (openRectangle_isOpen a b c d).measurableSet] with x hx hz hxU
    change h3Value U (q3H3RemainderMap a b c d β L x₀ z) x = (0 : Lp ℝ 2 (volume.restrict U)) x
    rw [hx]
    have hxK : x ∈ closedRectangle a b c d :=
      ⟨Ioo_subset_Icc_self hxU.1, Ioo_subset_Icc_self hxU.2⟩
    rw [hval ⟨x, hxK⟩, hj, hu, ContinuousMap.zero_apply, hz]
    rfl

/-- This is the source carrier (ker (R K))ᗮ with the white-noise norm, rather than the
ordinary-H³ closure norm. Its physical fields are given by `cameronMartinField`. -/
abbrev Q3RemainderCameronMartin := CameronMartin (q3RemainderH3Factor a b c d β L x₀)

end
end ASDExplicitGamma.Gaussian
