module

public import ASDExplicitGamma.Gaussian.Q3SobolevOperator
public import ASDExplicitGamma.Gaussian.RectangleDomain
public import ASDExplicitGamma.Gaussian.RectangleSobolev

/-! # The rectangular H³ estimate on actual q3 convolution directions -/

@[expose] public section

open MeasureTheory Homogenization Set
open scoped Topology

namespace ASDExplicitGamma.Gaussian

private theorem q3Convolution_deriv_first (b : ℝ) (L : {l : ℝ // 0 < l}) (a : H3Index)
    (ha : a.1.1.val + a.1.2.val ≤ 2) (u : WhiteNoise) (s t : ℝ) :
    HasDerivAt (fun r => q3Convolution b L a u ![r, t])
      (q3Convolution b L (h3Next a 0 ha) u ![s, t]) s := by
  have hl : HasDerivAt (fun r : ℝ => (![r, t] : Vec 2)) (basisVec 0) s := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · convert hasDerivAt_id s using 1 <;> rfl
    · simpa [basisVec] using hasDerivAt_const s t
  have hh := (q3Convolution_hasFDerivAt b L a ha u ![s, t]).comp_hasDerivAt s hl
  convert hh using 1 <;> first | rfl | simp [basisVec, ContinuousLinearMap.proj_apply]

private theorem q3Convolution_deriv_second (b : ℝ) (L : {l : ℝ // 0 < l}) (a : H3Index)
    (ha : a.1.1.val + a.1.2.val ≤ 2) (u : WhiteNoise) (s t : ℝ) :
    HasDerivAt (fun r => q3Convolution b L a u ![s, r])
      (q3Convolution b L (h3Next a 1 ha) u ![s, t]) t := by
  have hl : HasDerivAt (fun r : ℝ => (![s, r] : Vec 2)) (basisVec 1) t := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa [basisVec] using hasDerivAt_const t s
    · convert hasDerivAt_id t using 1 <;> rfl
  have hh := (q3Convolution_hasFDerivAt b L a ha u ![s, t]).comp_hasDerivAt t hl
  convert hh using 1 <;> first | rfl | simp [basisVec, ContinuousLinearMap.proj_apply]

/-- Every rectangular L² coordinate is bounded by the full ordinary weak H³ norm. -/
theorem q3Convolution_rectangle_integral_le (a b c d β : ℝ) (L : {l : ℝ // 0 < l})
    (v : WhiteNoise) (i : H3Index) :
    (∫ s in Icc a b, ∫ t in Icc c d, q3Convolution β L i v ![s, t] ^ 2) ≤
      ‖q3SobolevOperator (openRectangle a b c d) β L v‖ ^ 2 := by
  let U := openRectangle a b c d
  have he : (∫ x in U, q3Convolution β L i v x ^ 2) =
      ‖q3Coordinate U β L i v‖ ^ 2 := by
    rw [l2_norm_sq]
    apply integral_congr_ae
    filter_upwards [q3Coordinate_ae U β L i v] with x hx
    change _ = ‖q3Coordinate U β L i v x‖ ^ 2
    rw [hx, Real.norm_eq_abs, sq_abs]
    rfl
  rw [← rectangle_integral_eq a b c d (fun x => q3Convolution β L i v x ^ 2) ((q3Convolution_continuous β L i v).pow 2), he]
  exact pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le
    (q3SobolevOperator U β L v).1 i) 2

/-- On a nondegenerate source rectangle, the value and each first partial have a uniform
pointwise bound by the actual ordinary weak H³ norm. -/
theorem q3Convolution_point_sq_le (a b c d β : ℝ) (hab : a < b) (hcd : c < d)
    (L : {l : ℝ // 0 < l}) (v : WhiteNoise) (i : H3Index)
    (hi : i.1.1.val + i.1.2.val ≤ 1) (s t : ℝ) (hs : s ∈ Icc a b) (ht : t ∈ Icc c d) :
    q3Convolution β L i v ![s, t] ^ 2 ≤
      ((2 / (b - a)) * (2 / (d - c)) + (2 * (b - a)) * (2 / (d - c)) +
        (2 / (b - a)) * (2 * (d - c)) + (2 * (b - a)) * (2 * (d - c))) *
        ‖q3SobolevOperator (openRectangle a b c d) β L v‖ ^ 2 := by
  have hi2 : i.1.1.val + i.1.2.val ≤ 2 := by omega
  let i₁ := h3Next i 0 hi2
  let i₂ := h3Next i 1 hi2
  have hi₁ : i₁.1.1.val + i₁.1.2.val ≤ 2 := by dsimp [i₁, h3Next]; omega
  let i₁₂ := h3Next i₁ 1 hi₁
  let f (j : H3Index) := fun s t => q3Convolution β L j v ![s, t]
  have hcont (j : H3Index) : Continuous (Function.uncurry (f j)) := by
    apply (q3Convolution_continuous β L j v).comp
    fun_prop
  have hsmooth (j : H3Index) (hj : j.1.1.val + j.1.2.val ≤ 2) :
      (∀ t, ContDiff ℝ 1 (fun s => f j s t)) ∧ (∀ s, ContDiff ℝ 1 (f j s)) := by
    constructor <;> intro r <;> apply (q3Convolution_contDiff_one β L j hj v).comp
    all_goals apply contDiff_pi.mpr; intro k; fin_cases k <;> simpa using (by fun_prop)
  have hh := rectangle_value_sq_le hab hcd hs ht (f i) (f i₁) (f i₂) (f i₁₂)
    (hcont i) (hcont i₁) (hcont i₂) (hcont i₁₂)
    (hsmooth i hi2).1 (hsmooth i hi2).2 (hsmooth i₁ hi₁).2
    (fun t => funext fun s => (q3Convolution_deriv_first β L i hi2 v s t).deriv)
    (fun s => funext fun t => (q3Convolution_deriv_second β L i hi2 v s t).deriv)
    (fun s => funext fun t => (q3Convolution_deriv_second β L i₁ hi₁ v s t).deriv)
  have hnorm (j : H3Index) := q3Convolution_rectangle_integral_le a b c d β L v j
  have hA : 0 ≤ 2 / (b - a) := div_nonneg (by norm_num) (sub_pos.mpr hab).le
  have hB : 0 ≤ 2 * (b - a) := mul_nonneg (by norm_num) (sub_pos.mpr hab).le
  have hC : 0 ≤ 2 / (d - c) := div_nonneg (by norm_num) (sub_pos.mpr hcd).le
  have hD : 0 ≤ 2 * (d - c) := mul_nonneg (by norm_num) (sub_pos.mpr hcd).le
  calc
    _ ≤ _ := hh
    _ ≤ _ := add_le_add (add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left (hnorm i) (mul_nonneg hA hC))
      (mul_le_mul_of_nonneg_left (hnorm i₁) (mul_nonneg hB hC)))
      (mul_le_mul_of_nonneg_left (hnorm i₂) (mul_nonneg hA hD)))
      (mul_le_mul_of_nonneg_left (hnorm i₁₂) (mul_nonneg hB hD))
    _ = _ := by ring

end ASDExplicitGamma.Gaussian
