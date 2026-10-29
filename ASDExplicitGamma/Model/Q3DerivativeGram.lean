module

public import ASDExplicitGamma.Model.Q3DerivativeMoments

/-! Literal spatial derivative covariance rows, retaining each shell variance and length. -/

@[expose] public section
namespace ASDExplicitGamma.Model
open Homogenization
open scoped BigOperators
noncomputable section

 theorem q3Cov_odd_derivatives_zero : iteratedDeriv 1 q3Cov 0 = 0 ∧ iteratedDeriv 3 q3Cov 0 = 0 := by
  have he : (fun x => q3Cov (-x)) = q3Cov := funext q3Cov_even
  have h1 := iteratedDeriv_comp_neg 1 q3Cov (0:ℝ)
  have h3 := iteratedDeriv_comp_neg 3 q3Cov (0:ℝ)
  rw [he] at h1 h3
  norm_num at h1 h3
  exact ⟨by simpa only [iteratedDeriv_one] using (show deriv q3Cov 0 = 0 by linarith only [h1]), by linarith only [h3]⟩

inductive Q3SpatialJet where
  | value
  | first (i : Fin 2)
  | second (i j : Fin 2)
  deriving DecidableEq

 def Q3SpatialJet.count : Q3SpatialJet → Fin 2 → ℕ
  | .value, _ => 0
  | .first i, a => if i=a then 1 else 0
  | .second i j, a => (if i=a then 1 else 0)+(if j=a then 1 else 0)

 def Q3SpatialJet.order (o : Q3SpatialJet) : ℕ := o.count 0+o.count 1

/-- Derivatives in the second argument carry the stationary covariance sign. -/
def q3ScaledJetCovariance (v L : ℝ) (o p : Q3SpatialJet) (x y : Vec 2) : ℝ :=
  v*(-1:ℝ)^p.order / L^(o.order+p.order) *
    q3CovariancePartial (o.count 0+p.count 0) (o.count 1+p.count 1)
      ((x 0-y 0)/L) ((x 1-y 1)/L)

 def q3BandJetCovariance {ι : Type*} (s : Finset ι) (v L : ι → ℝ)
    (o p : Q3SpatialJet) (x y : Vec 2) : ℝ :=
  ∑ k ∈ s, q3ScaledJetCovariance (v k) (L k) o p x y

 def q3BandMoment {ι : Type*} (s : Finset ι) (v L : ι → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ s, v k/(L k)^n

 theorem q3ScaledJetCovariance_value_diagonal (v L : ℝ) (x : Vec 2) :
    q3ScaledJetCovariance v L .value .value x x = v := by
  norm_num [q3ScaledJetCovariance, Q3SpatialJet.order, Q3SpatialJet.count,
    q3CovariancePartial_eq, q3Cov_at_zero, iteratedDeriv_zero]

 theorem q3ScaledJetCovariance_first_diagonal (v L : ℝ) (x : Vec 2) (i j : Fin 2) :
    q3ScaledJetCovariance v L (.first i) (.first j) x x =
      if i=j then (78/5:ℝ)*v/L^2 else 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [q3ScaledJetCovariance, Q3SpatialJet.order, Q3SpatialJet.count,
      q3CovariancePartial_eq, q3Cov_at_zero, iteratedDeriv_zero,
      q3Cov_iteratedDeriv_values.1, q3Cov_odd_derivatives_zero.1] <;> ring

 theorem q3ScaledJetCovariance_second_diagonal (v L : ℝ) (x : Vec 2) (i j a b : Fin 2) :
    q3ScaledJetCovariance v L (.second i j) (.second a b) x x =
      (if i=0 then if j=0 then if a=0 then if b=0 then (3432/5:ℝ) else 0
        else if b=1 then (78/5:ℝ)^2 else 0
      else if a=0 then if b=1 then (78/5:ℝ)^2 else 0
        else if b=0 then (78/5:ℝ)^2 else 0
      else if j=0 then if a=0 then if b=1 then (78/5:ℝ)^2 else 0
        else if b=0 then (78/5:ℝ)^2 else 0
      else if a=0 then if b=0 then (78/5:ℝ)^2 else 0
        else if b=1 then (3432/5:ℝ) else 0) * v/L^4 := by
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    norm_num [q3ScaledJetCovariance, Q3SpatialJet.order, Q3SpatialJet.count,
      q3CovariancePartial_eq, q3Cov_at_zero, iteratedDeriv_zero,
      q3Cov_iteratedDeriv_values.1, q3Cov_iteratedDeriv_values.2.1,
      q3Cov_odd_derivatives_zero.1, q3Cov_odd_derivatives_zero.2] <;> ring

 theorem q3BandMoment_nonneg {ι : Type*} (s : Finset ι) (v L : ι → ℝ) (n : ℕ)
    (hv : ∀ k ∈ s, 0 ≤ v k) (hL : ∀ k ∈ s, 0 < L k) : 0 ≤ q3BandMoment s v L n := by
  exact Finset.sum_nonneg fun k hk => div_nonneg (hv k hk) (pow_nonneg (hL k hk).le _)

 theorem q3ScaledJetCovariance_first_quadratic (v L : ℝ) (x : Vec 2) (a : Fin 2 → ℝ) :
    (∑ i, ∑ j, a i*a j*q3ScaledJetCovariance v L (.first i) (.first j) x x) =
      (78/5:ℝ)*(v/L^2)*(∑ i, a i^2) := by
  simp only [q3ScaledJetCovariance_first_diagonal, Fin.sum_univ_two]
  norm_num
  ring

 theorem q3ScaledJetCovariance_second_quadratic (v L : ℝ) (x : Vec 2)
    (a : Fin 2 × Fin 2 → ℝ) :
    (∑ i, ∑ j, a i*a j*q3ScaledJetCovariance v L (.second i.1 i.2) (.second j.1 j.2) x x) =
      (v/L^4)*((3432/5:ℝ)*(a (0,0)^2+a (1,1)^2)+
        2*(78/5:ℝ)^2*a (0,0)*a (1,1)+(78/5:ℝ)^2*(a (0,1)+a (1,0))^2) := by
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, q3ScaledJetCovariance_second_diagonal]
  norm_num
  ring

 theorem q3ScaledJetCovariance_second_quadratic_le {v : ℝ} (hv : 0 ≤ v) (L : ℝ)
    (x : Vec 2) (a : Fin 2 × Fin 2 → ℝ) :
    (∑ i, ∑ j, a i*a j*q3ScaledJetCovariance v L (.second i.1 i.2) (.second j.1 j.2) x x) ≤
      ((3432/5:ℝ)+(78/5:ℝ)^2)*(v/L^4)*(∑ i, a i^2) := by
  rw [q3ScaledJetCovariance_second_quadratic]
  have hh : (3432/5:ℝ)*(a (0,0)^2+a (1,1)^2)+2*(78/5:ℝ)^2*a (0,0)*a (1,1)+
      (78/5:ℝ)^2*(a (0,1)+a (1,0))^2 ≤
      ((3432/5:ℝ)+(78/5:ℝ)^2)*(∑ i, a i^2) := by
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
    nlinarith only [sq_nonneg (a (0,0)-a (1,1)), sq_nonneg (a (0,1)-a (1,0)),
      sq_nonneg (a (0,1)), sq_nonneg (a (1,0))]
  convert mul_le_mul_of_nonneg_left hh (div_nonneg hv (pow_nonneg (sq_nonneg L) 2)) using 1 <;> ring

end
end ASDExplicitGamma.Model
