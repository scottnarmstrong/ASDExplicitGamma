module

public import ASDExplicitGamma.Cold.ColdScalingAlgebra

/-! # Proportional scaling of the two optimized cold graph candidates -/

@[expose] public section
noncomputable section
namespace ASDExplicitGamma.Cold

/-- A proportional nonnegative scalar input is at most its sqrt(theta) scaling. -/
theorem cold_scale_le_sqrt {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) : θ ≤ Real.sqrt θ := by
  have he := Real.sq_sqrt hθ
  have ht : θ^2 ≤ θ := by nlinarith only [hθ,hθ1]
  exact (sq_le_sq₀ hθ (Real.sqrt_nonneg _)).mp (by rw [he]; exact ht)

/-- A nonnegative quadratic radical scales exactly under proportional inputs. -/
theorem cold_sqrt_quadratic_scale {θ x : ℝ} (hθ : 0 ≤ θ) :
    Real.sqrt (θ^2*x) = θ*Real.sqrt x := by
  rw [Real.sqrt_mul (sq_nonneg θ),Real.sqrt_sq_eq_abs,abs_of_nonneg hθ]

/-- The full five-sixths graph candidate scales by at most theta. -/
theorem cold_five_sixths_scale {θ D L c : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hc : 0 ≤ c) :
    2*(c*Real.sqrt (2*(θ*D)+(θ*L)^2)+Real.sqrt ((5/6:ℝ)*(θ*D)^2+c^2*(θ*L)^2))^2 ≤
      θ*(2*(c*Real.sqrt (2*D+L^2)+Real.sqrt ((5/6:ℝ)*D^2+c^2*L^2))^2) := by
  have he := mul_le_mul_of_nonneg_left (cold_spectral_radical_scale hθ hθ1 (D := D) (L := L)) hc
  have hr : (5/6:ℝ)*(θ*D)^2+c^2*(θ*L)^2 = θ^2*((5/6:ℝ)*D^2+c^2*L^2) := by ring
  have hh := mul_le_mul_of_nonneg_right (cold_scale_le_sqrt hθ hθ1) (Real.sqrt_nonneg ((5/6:ℝ)*D^2+c^2*L^2))
  rw [hr,cold_sqrt_quadratic_scale hθ]
  apply cold_graph_square_scale hθ (by positivity) (by positivity)
  nlinarith only [he,hh]

/-- The full in-grid half-floor sandwich candidate scales by at most theta. -/
theorem cold_sandwich_scale {θ D L c : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hD : 0 ≤ D) (hc : 0 ≤ c) :
    let eθ := c*Real.sqrt (2*(θ*D)+(θ*L)^2)
    let e := c*Real.sqrt (2*D+L^2)
    2*(eθ+Real.sqrt ((θ*D)^2/2+2*eθ^2))^2 ≤
      θ*(2*(e+Real.sqrt (D^2/2+2*e^2))^2) := by
  dsimp only
  have he := mul_le_mul_of_nonneg_left (cold_spectral_radical_scale hθ hθ1 (D := D) (L := L)) hc
  have hsθ : (c*Real.sqrt (2*(θ*D)+(θ*L)^2))^2 = c^2*(2*(θ*D)+(θ*L)^2) := by
    rw [mul_pow,Real.sq_sqrt (by positivity)]
  have hs : (c*Real.sqrt (2*D+L^2))^2 = c^2*(2*D+L^2) := by
    rw [mul_pow,Real.sq_sqrt (by positivity)]
  have hrθ : (θ*D)^2/2+2*(c*Real.sqrt (2*(θ*D)+(θ*L)^2))^2 =
      θ^2*(D^2/2+2*c^2*L^2)+θ*(4*c^2*D) := by rw [hsθ]; ring
  have hr : D^2/2+2*(c*Real.sqrt (2*D+L^2))^2 =
      (D^2/2+2*c^2*L^2)+(4*c^2*D) := by rw [hs]; ring
  have hh := cold_quadratic_radical_scale hθ hθ1
    (show 0 ≤ D^2/2+2*c^2*L^2 by positivity) (b := 4*c^2*D)
  rw [hrθ,hr]
  apply cold_graph_square_scale hθ (by positivity) (by positivity)
  nlinarith only [he,hh]

/-- The old graph candidate, including its global branch, scales by at most theta. -/
theorem cold_old_graph_scale {θ a L c : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (ha : 0 ≤ a) (hL : 0 ≤ L) (hc : 0 ≤ c) :
    min (2*(2*(θ*a)+2*(Real.sqrt (2*(θ*a)+(θ*L)^2)+θ*L)*c)^2)
      (4*(θ*a+(θ*L)^2)) ≤
    θ*min (2*(2*a+2*(Real.sqrt (2*a+L^2)+L)*c)^2) (4*(a+L^2)) := by
  rw [mul_min_of_nonneg _ _ hθ]
  apply min_le_min
  · apply cold_graph_square_scale hθ (by positivity) (by positivity)
    have hs := cold_spectral_radical_scale hθ hθ1 (D := a) (L := L)
    have ht := cold_scale_le_sqrt hθ hθ1
    have hsa := mul_le_mul_of_nonneg_right ht ha
    have hsL := mul_le_mul_of_nonneg_right ht hL
    have hsum := mul_le_mul_of_nonneg_right (add_le_add hs hsL) hc
    nlinarith only [hsa,hsum]
  · have ht : θ^2 ≤ θ := by nlinarith only [hθ,hθ1]
    have hm := mul_le_mul_of_nonneg_right ht (sq_nonneg L)
    nlinarith only [hm]

end ASDExplicitGamma.Cold
