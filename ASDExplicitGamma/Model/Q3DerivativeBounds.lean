module

public import ASDExplicitGamma.Model.Q3DerivativeSmooth
public import ASDExplicitGamma.Model.Q3DerivativeIncrement

/-! Exact global one-dimensional derivative certificate used by the canonical single direction. -/

@[expose] public section
namespace ASDExplicitGamma.Model
open Filter Set Topology
noncomputable section

 theorem q3Cov_derivative_combined_unit {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (iteratedDeriv 2 q3Cov t)^2+(78/5:ℝ)*(iteratedDeriv 1 q3Cov t)^2 ≤ (78/5:ℝ)^2 := by
  rw [q3Cov_iteratedDeriv_eq_rightPolynomial (by norm_num : 2 ≤ 2) ht ht1,
    q3Cov_iteratedDeriv_eq_rightPolynomial (by norm_num : 1 ≤ 2) ht ht1]
  have h1 : 0 ≤ 1-t := sub_nonneg.mpr ht1
  have he : (78/5:ℝ)^2 - (((Polynomial.derivative^[2]) q3CovRightPolynomial).eval t)^2 -
      (78/5:ℝ)*(((Polynomial.derivative^[1]) q3CovRightPolynomial).eval t)^2 =
    t^2*((863928/125:ℝ)*t^0*(1-t)^24 +
      (20734272/125:ℝ)*t^1*(1-t)^23 +
      (220642344/125:ℝ)*t^2*(1-t)^22 +
      (1371005064/125:ℝ)*t^3*(1-t)^21 +
      (1105406016/25:ℝ)*t^4*(1-t)^20 +
      (15256485816/125:ℝ)*t^5*(1-t)^19 +
      (29983268172/125:ℝ)*t^6*(1-t)^18 +
      (44745921792/125:ℝ)*t^7*(1-t)^17 +
      (59727394584/125:ℝ)*t^8*(1-t)^16 +
      (17939258064/25:ℝ)*t^9*(1-t)^15 +
      (147588376338/125:ℝ)*t^10*(1-t)^14 +
      (42886243764/25:ℝ)*t^11*(1-t)^13 +
      (246705497298/125:ℝ)*t^12*(1-t)^12 +
      (44408770848/25:ℝ)*t^13*(1-t)^11 +
      (31991947416/25:ℝ)*t^14*(1-t)^10 +
      (760390488/1:ℝ)*t^15*(1-t)^9 +
      (380195244/1:ℝ)*t^16*(1-t)^8 +
      (160082208/1:ℝ)*t^17*(1-t)^7 +
      (280143864/5:ℝ)*t^18*(1-t)^6 +
      (80041104/5:ℝ)*t^19*(1-t)^5 +
      (3638232/1:ℝ)*t^20*(1-t)^4 +
      (632736/1:ℝ)*t^21*(1-t)^3 +
      (79092/1:ℝ)*t^22*(1-t)^2 +
      (158184/25:ℝ)*t^23*(1-t)^1 +
      (6084/25:ℝ)*t^24*(1-t)^0) := by
    norm_num [q3CovRightPolynomial, Polynomial.derivative_X_pow]
    ring
  have hp : 0 ≤ (78/5:ℝ)^2 - (((Polynomial.derivative^[2]) q3CovRightPolynomial).eval t)^2 -
      (78/5:ℝ)*(((Polynomial.derivative^[1]) q3CovRightPolynomial).eval t)^2 := by
    rw [he]
    positivity
  linarith only [hp]

 theorem q3Cov_derivative_sq_abs (x : ℝ) :
    (iteratedDeriv 1 q3Cov |x|)^2 = (iteratedDeriv 1 q3Cov x)^2 ∧
    (iteratedDeriv 2 q3Cov |x|)^2 = (iteratedDeriv 2 q3Cov x)^2 := by
  rcases le_total 0 x with hx | hx
  · simp only [abs_of_nonneg hx, and_self]
  · rw [abs_of_nonpos hx]
    have h1 := iteratedDeriv_comp_neg 1 q3Cov x
    have h2 := iteratedDeriv_comp_neg 2 q3Cov x
    rw [show (fun x => q3Cov (-x)) = q3Cov from funext q3Cov_even] at h1 h2
    norm_num only [pow_one, neg_one_smul, neg_one_sq, one_smul] at h1 h2
    constructor
    · rw [← neg_eq_iff_eq_neg.mpr h1, neg_sq]
    · rw [h2]

 theorem q3Cov_derivative_combined (x : ℝ) :
    (iteratedDeriv 2 q3Cov x)^2+(78/5:ℝ)*(iteratedDeriv 1 q3Cov x)^2 ≤ (78/5:ℝ)^2 := by
  by_cases hx : |x| ≤ 1
  · have h := q3Cov_derivative_combined_unit (abs_nonneg x) hx
    simpa only [(q3Cov_derivative_sq_abs x).1, (q3Cov_derivative_sq_abs x).2] using h
  · have he : q3Cov =ᶠ[𝓝 x] (fun _ => (0:ℝ)) := by
      filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds (lt_of_not_ge hx)] with y hy
      exact q3Cov_zero_of_abs_ge_one hy.le
    rw [he.iteratedDeriv_eq 1, he.iteratedDeriv_eq 2]
    norm_num

 theorem q3Cov_nonneg (x : ℝ) : 0 ≤ q3Cov x := by
  apply MeasureTheory.integral_nonneg
  intro y
  change 0 ≤ q3Kernel y*q3Kernel (y+x)
  apply mul_nonneg <;> unfold q3Kernel <;> split_ifs with hy
  · obtain ⟨hl,hr⟩ := abs_le.mp hy
    have hb : 0 ≤ 1-4*y^2 := by nlinarith
    positivity
  · exact le_rfl
  · obtain ⟨hl,hr⟩ := abs_le.mp hy
    have hb : 0 ≤ 1-4*(y+x)^2 := by nlinarith
    positivity
  · exact le_rfl

 theorem q3Cov_sq_le_one (x : ℝ) : (q3Cov x)^2 ≤ 1 := by
  have hlo := q3Cov_nonneg x
  have hhi := (q3Cov_quadratic_bounds x).2
  nlinarith only [hlo,hhi]

end
end ASDExplicitGamma.Model
