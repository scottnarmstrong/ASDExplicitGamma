module

public import ASDExplicitGamma.Gaussian.SupMeanFirstCovariance

/-! Coordinate derivative algebra for the literal product covariance, without a
spurious global smoothness assumption on higher covariance derivatives. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization
noncomputable section

/-- Ordinary derivative along one coordinate at the specified point. -/
def supMeanCoordinateDerivative (i : Fin 2) (f : Vec 2 → ℝ) (x : Vec 2) : ℝ :=
  deriv (fun t : ℝ => f (x+t • basisVec i)) 0

/-- The product covariance jet before its physical amplitude and length are restored. -/
def supMeanProductJet (a b : ℕ) (c : ℝ) (x y : Vec 2) : ℝ :=
  iteratedDeriv a ASDExplicitGamma.q3Cov (c*(x 0-y 0)) *
    iteratedDeriv b ASDExplicitGamma.q3Cov (c*(x 1-y 1))

/-- Affine reparametrization is valid even when the derivative does not exist:
the total derivative convention is respected also at slope zero. -/
theorem supMean_deriv_affine_zero (f : ℝ → ℝ) (a b : ℝ) :
    deriv (fun t : ℝ => f (a+b*t)) 0 = b*deriv f a := by
  simpa only [deriv_comp_const_add, mul_zero, add_zero, smul_eq_mul] using
    deriv_comp_mul_left b (fun t => f (a+t)) 0

/-- Each first-argument coordinate derivative raises exactly its own product jet. -/
theorem supMean_product_jet_left (a b : ℕ) (c : ℝ) (x y : Vec 2) (i : Fin 2) :
    supMeanCoordinateDerivative i (fun z => supMeanProductJet a b c z y) x =
      c*supMeanProductJet (a+if i=0 then 1 else 0) (b+if i=1 then 1 else 0) c x y := by
  fin_cases i
  · norm_num [supMeanCoordinateDerivative, supMeanProductJet, basisVec_apply,
      deriv_mul_const_field]
    have hfun : (fun t : ℝ => iteratedDeriv a ASDExplicitGamma.q3Cov
        (c*(x 0+t-y 0))) = (fun t => iteratedDeriv a ASDExplicitGamma.q3Cov
          (c*(x 0-y 0)+c*t)) := by funext t; congr 1; ring
    rw [hfun, supMean_deriv_affine_zero, ← iteratedDeriv_succ]
    ring
  · norm_num [supMeanCoordinateDerivative, supMeanProductJet, basisVec_apply,
      deriv_const_mul_field]
    have hfun : (fun t : ℝ => iteratedDeriv b ASDExplicitGamma.q3Cov
        (c*(x 1+t-y 1))) = (fun t => iteratedDeriv b ASDExplicitGamma.q3Cov
          (c*(x 1-y 1)+c*t)) := by funext t; congr 1; ring
    rw [hfun, supMean_deriv_affine_zero, ← iteratedDeriv_succ]
    ring

/-- Swapping covariance arguments reverses the coordinate scale. -/
theorem supMean_product_jet_swap (a b : ℕ) (c : ℝ) (x y : Vec 2) :
    supMeanProductJet a b (-c) y x = supMeanProductJet a b c x y := by
  unfold supMeanProductJet
  congr 1 <;> congr 1 <;> ring

/-- Constant scalar multiplication commutes with the total coordinate derivative. -/
theorem supMean_coordinate_derivative_const_mul (i : Fin 2) (A : ℝ)
    (f : Vec 2 → ℝ) (x : Vec 2) :
    supMeanCoordinateDerivative i (fun z => A*f z) x = A*supMeanCoordinateDerivative i f x := by
  exact deriv_const_mul_field A

end
end ASDExplicitGamma.Gaussian
