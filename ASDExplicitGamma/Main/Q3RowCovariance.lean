module

public import ASDExplicitGamma.Main.Q3JetGram
public import ASDExplicitGamma.Model.Q3DerivativeBand
public import ASDExplicitGamma.Triadic.FiniteGramBounds

/-! Sharp operator bounds for actual q3 covariance rows. -/

@[expose] public section
namespace ASDExplicitGamma.Main
open Homogenization ASDExplicitGamma.Gaussian ASDExplicitGamma.Model ASDExplicitGamma.Triadic
open scoped BigOperators RealInnerProductSpace

/-- Actual countable covariance rows at a point, rather than a covariance
identification hypothesis. -/
theorem main_q3_jet_covariance {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (b : ℝ) (L : {l : ℝ // 0 < l}) (o p : Q3SpatialJet) (x : Vec 2) :
    HasSum (fun j => q3Convolution b L (mainQ3JetIndex o) (e j) x*
      q3Convolution b L (mainQ3JetIndex p) (e j) x)
      (q3ScaledJetCovariance (b^2) L.1 o p x x) := by
  rw [← main_q3_jet_gram]
  exact main_q3_direction_covariance e b L _ _ x x

/-- The first-derivative ROW bound is 15.6, rather than the column trace 31.2. -/
theorem main_q3_first_row_bound {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (s : Finset ι) (c : ι → ℝ) (b : ℝ) (L : {l : ℝ // 0 < l}) (x : Vec 2) :
    (∑ i : Fin 2, (∑ j ∈ s, c j*q3Convolution b L (mainQ3JetIndex (.first i)) (e j) x)^2) ≤
      ((78/5)*b^2/L.1^2)*(∑ j ∈ s, c j^2) := by
  apply finite_vector_coefficient_sq_bound
    (fun j i => q3Convolution b L (mainQ3JetIndex (.first i)) (e j) x)
    (fun i k => q3ScaledJetCovariance (b^2) L.1 (.first i) (.first k) x x)
    (fun i k => (main_q3_jet_covariance e b L (.first i) (.first k) x).summable)
    (fun i k => (main_q3_jet_covariance e b L (.first i) (.first k) x).tsum_eq)
    (by positivity)
  intro a
  rw [q3ScaledJetCovariance_first_quadratic]
  exact le_of_eq (by ring)

/-- The second-derivative ROW uses the sharp covariance operator bound 929.76,
whereas its full column Frobenius trace is 1859.52. -/
theorem main_q3_second_row_bound {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (s : Finset ι) (c : ι → ℝ) (b : ℝ) (L : {l : ℝ // 0 < l}) (x : Vec 2) :
    (∑ i : Fin 2 × Fin 2,
      (∑ j ∈ s, c j*q3Convolution b L (mainQ3JetIndex (.second i.1 i.2)) (e j) x)^2) ≤
      ((23244/25)*b^2/L.1^4)*(∑ j ∈ s, c j^2) := by
  apply finite_vector_coefficient_sq_bound
    (fun j (i : Fin 2 × Fin 2) =>
      q3Convolution b L (mainQ3JetIndex (.second i.1 i.2)) (e j) x)
    (fun i k => q3ScaledJetCovariance (b^2) L.1 (.second i.1 i.2) (.second k.1 k.2) x x)
    (fun i k => (main_q3_jet_covariance e b L (.second i.1 i.2) (.second k.1 k.2) x).summable)
    (fun i k => (main_q3_jet_covariance e b L (.second i.1 i.2) (.second k.1 k.2) x).tsum_eq)
    (by positivity)
  intro a
  have h := q3ScaledJetCovariance_second_quadratic_le (sq_nonneg b) L.1 x a
  norm_num at h
  convert h using 1; ring

end ASDExplicitGamma.Main
