module

public import ASDExplicitGamma.Variational.LemmaVH2SingleFunction

/-! The three sharp, canonical covariance-defect caps of SHEAR (3.2). -/

@[expose] public section
namespace ASDExplicitGamma.Variational
open Homogenization MeasureTheory ASDExplicitGamma.Model ASDExplicitGamma.Triadic
open scoped BigOperators
noncomputable section

 theorem q3CovarianceDefect_value_cap (Q : TriadicCube 2) (L : ℝ) {x : Vec 2} (hx : x ∈ cubeSet Q) :
    |q3CovarianceDefect L (cubeCenter Q) x| ≤ (lemmaVH2R1/4)*(cubeScaleFactor Q/L)^2 := by
  have hp : q3ProductCovariance (fun i => (x i-cubeCenter Q i)/L) ≤ 1 := by
    unfold q3ProductCovariance
    simpa only [one_mul] using mul_le_mul
      (q3Cov_quadratic_bounds ((x 0-cubeCenter Q 0)/L)).2
      (q3Cov_quadratic_bounds ((x 1-cubeCenter Q 1)/L)).2
      (q3Cov_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  have hs := q3RemainderJetCovariance_value_cap (v := 1) (by norm_num) Q (L := L) hx
  rw [q3RemainderJetCovariance_value_diagonal] at hs
  unfold q3CovarianceDefect
  rw [abs_of_nonpos (sub_nonpos.mpr hp)]
  nlinarith only [hs]

 theorem q3CovarianceDefectGradient_sq_bound (L : ℝ) (z x : Vec 2) :
    (∑ i, (q3CovarianceDefectGradient L z x i)^2) ≤
      (78/5:ℝ)^2/L^4*((x 0-z 0)^2+(x 1-z 1)^2) := by
  have hi (a b : ℝ) : (deriv q3Cov a*q3Cov b)^2 ≤ (78/5:ℝ)^2*a^2 := by
    have h1 := mul_le_mul_of_nonneg_left (q3Cov_sq_le_one b) (sq_nonneg (deriv q3Cov a))
    have h2 := (sq_le_sq₀ (abs_nonneg (deriv q3Cov a))
      (mul_nonneg (by norm_num : (0:ℝ) ≤ 78/5) (abs_nonneg a))).2 (q3Cov_first_abs_le a)
    simp only [sq_abs, mul_pow] at h2 ⊢
    nlinarith only [h1,h2]
  have h0 := div_le_div_of_nonneg_right (hi ((x 0-z 0)/L) ((x 1-z 1)/L)) (sq_nonneg L)
  have h1 := div_le_div_of_nonneg_right (hi ((x 1-z 1)/L) ((x 0-z 0)/L)) (sq_nonneg L)
  simp only [Fin.sum_univ_two, q3CovarianceDefectGradient]
  norm_num only [Fin.zero_eta, Fin.isValue, ite_true, show (1:Fin 2) ≠ 0 by decide, ite_false]
  convert add_le_add h0 h1 using 1 <;> simp only [div_pow] <;> ring

 theorem q3CovarianceDefect_gradient_cap (Q : TriadicCube 2) {L : ℝ} (hL : 0 < L)
    {x : Vec 2} (hx : x ∈ cubeSet Q) :
    planarEuclideanNorm (planarW1Value (q3CovarianceDefectWitness Q L (cubeCenter Q)).gradient x) ≤
      (lemmaVH2R1/Real.sqrt 2)*(cubeScaleFactor Q/L)/L := by
  rw [q3CovarianceDefectWitness_gradient]
  have hsq := (q3CovarianceDefectGradient_sq_bound L (cubeCenter Q) x).trans
    (mul_le_mul_of_nonneg_left (planar_cube_center_distance_sq Q hx)
      (div_nonneg (sq_nonneg (78/5:ℝ)) (pow_nonneg hL.le 4)))
  unfold planarEuclideanNorm
  apply (Real.sqrt_le_iff).2
  constructor
  · have hS := (ASDExplicitGamma.Triadic.cubeScaleFactor_pos' Q).le
    unfold lemmaVH2R1
    positivity
  · convert hsq using 1
    unfold lemmaVH2R1
    have h2 : (Real.sqrt 2)^2 = (2:ℝ) := Real.sq_sqrt (by norm_num)
    simp only [div_pow, mul_pow, h2]
    ring

 theorem q3CovarianceDefectHessian_sq_bound (L : ℝ) (z x : Vec 2) :
    (∑ i, ∑ j, (q3CovarianceDefectHessian L z x i j)^2) ≤ 2*(78/5:ℝ)^2/L^4 := by
  have h := div_le_div_of_nonneg_right
    (q3CovProduct_hessian_sq_le ((x 0-z 0)/L) ((x 1-z 1)/L)) (pow_nonneg (sq_nonneg L) 2)
  convert h using 1 <;>
    simp only [q3CovarianceDefectHessian, Fin.sum_univ_two, div_pow] <;> norm_num <;> ring

 theorem q3CovarianceDefect_hessian_cap (Q : TriadicCube 2) {L : ℝ} (hL : 0 < L) (z x : Vec 2) :
    planarFrobeniusNorm (planarW1Derivative (q3CovarianceDefectWitness Q L z).gradient x) ≤
      lemmaVH2R1*Real.sqrt 2/L^2 := by
  rw [q3CovarianceDefectWitness_hessian]
  unfold planarFrobeniusNorm
  apply (Real.sqrt_le_iff).2
  constructor
  · unfold lemmaVH2R1
    positivity
  · convert q3CovarianceDefectHessian_sq_bound L z x using 1
    unfold lemmaVH2R1
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    ring

end
end ASDExplicitGamma.Variational
