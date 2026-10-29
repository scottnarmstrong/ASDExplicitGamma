module

public import ASDExplicitGamma.Model.Q3DerivativeGram

/-! Exact band covariance quadratic forms and their sharp derivative caps. -/

@[expose] public section
namespace ASDExplicitGamma.Model
open Homogenization
open scoped BigOperators
noncomputable section

 theorem q3BandJetCovariance_quadratic {ι κ : Type*} [Fintype κ]
    (s : Finset ι) (v L : ι → ℝ) (o : κ → Q3SpatialJet) (x y : Vec 2) (a : κ → ℝ) :
    (∑ i, ∑ j, a i*a j*q3BandJetCovariance s v L (o i) (o j) x y) =
      ∑ k ∈ s, ∑ i, ∑ j, a i*a j*q3ScaledJetCovariance (v k) (L k) (o i) (o j) x y := by
  simp only [q3BandJetCovariance, Finset.mul_sum]
  calc
    _ = ∑ i, ∑ k ∈ s, ∑ j, a i*a j*q3ScaledJetCovariance (v k) (L k) (o i) (o j) x y := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

 theorem q3BandJetCovariance_value_diagonal {ι : Type*} (s : Finset ι) (v L : ι → ℝ) (x : Vec 2) :
    q3BandJetCovariance s v L .value .value x x = q3BandMoment s v L 0 := by
  simp only [q3BandJetCovariance, q3ScaledJetCovariance_value_diagonal,
    q3BandMoment, pow_zero, div_one]

 theorem q3BandJetCovariance_first_quadratic {ι : Type*} (s : Finset ι) (v L : ι → ℝ)
    (x : Vec 2) (a : Fin 2 → ℝ) :
    (∑ i, ∑ j, a i*a j*q3BandJetCovariance s v L (.first i) (.first j) x x) =
      (78/5:ℝ)*q3BandMoment s v L 2*(∑ i, a i^2) := by
  rw [q3BandJetCovariance_quadratic]
  simp only [q3ScaledJetCovariance_first_quadratic, q3BandMoment]
  rw [← Finset.sum_mul, ← Finset.mul_sum]

 theorem q3BandJetCovariance_second_quadratic_le {ι : Type*} (s : Finset ι) (v L : ι → ℝ)
    (hv : ∀ k ∈ s, 0 ≤ v k) (x : Vec 2) (a : Fin 2 × Fin 2 → ℝ) :
    (∑ i, ∑ j, a i*a j*q3BandJetCovariance s v L (.second i.1 i.2) (.second j.1 j.2) x x) ≤
      ((3432/5:ℝ)+(78/5:ℝ)^2)*q3BandMoment s v L 4*(∑ i, a i^2) := by
  rw [q3BandJetCovariance_quadratic]
  convert Finset.sum_le_sum (fun k hk => q3ScaledJetCovariance_second_quadratic_le (hv k hk) (L k) x a) using 1
  simp only [q3BandMoment, ← Finset.sum_mul, ← Finset.mul_sum]

end
end ASDExplicitGamma.Model
