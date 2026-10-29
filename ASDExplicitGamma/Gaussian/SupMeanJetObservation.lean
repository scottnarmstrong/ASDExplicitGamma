module

public import ASDExplicitGamma.Gaussian.SupMeanCoordinateKernel
public import ASDExplicitGamma.Model.Q3DerivativeGram

/-! Coordinate observations identify the stored derivative law with the explicit product jets. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization ASDExplicitGamma.Model
noncomputable section

/-- The actual stored observation associated with a coordinate covariance jet. -/
def supMeanJetObservation (o : Q3SpatialJet) (x : Vec 2) : ShellDerivativeObservation :=
  match o with
  | .value => .value x
  | .first i => .first x (basisVec i)
  | .second i j => .second x (basisVec i) (basisVec j)

/-- A second observation is precisely two successive coordinate derivatives. -/
theorem supMean_second_observation_apply (i j : Fin 2) (x : Vec 2) (f : Vec 2 → ℝ) :
    shellObservationApply (.second x (basisVec i) (basisVec j)) f =
      supMeanCoordinateDerivative j (fun z => supMeanCoordinateDerivative i f z) x := rfl

/-- Each stored coordinate observation differentiates the literal first covariance
argument with its exact order and product-jet multiplicity. -/
theorem supMean_jet_observation_left (o : Q3SpatialJet) (a b : ℕ) (c : ℝ) (x y : Vec 2) :
    shellObservationApply (supMeanJetObservation o x) (fun z => supMeanProductJet a b c z y) =
      c^o.order * supMeanProductJet (a+o.count 0) (b+o.count 1) c x y := by
  cases o with
  | value => simp only [supMeanJetObservation, shellObservationApply, Q3SpatialJet.order,
      Q3SpatialJet.count, add_zero, pow_zero, one_mul]
  | first i =>
    change supMeanCoordinateDerivative i (fun z => supMeanProductJet a b c z y) x = _
    rw [supMean_product_jet_left]
    fin_cases i <;> norm_num [Q3SpatialJet.order, Q3SpatialJet.count]
  | second i j =>
    rw [supMeanJetObservation, supMean_second_observation_apply]
    have hf : (fun z => supMeanCoordinateDerivative i (fun u => supMeanProductJet a b c u y) z) =
        (fun z => c*supMeanProductJet (a+if i=0 then 1 else 0) (b+if i=1 then 1 else 0) c z y) := by
      funext z
      exact supMean_product_jet_left a b c z y i
    rw [hf, supMean_coordinate_derivative_const_mul, supMean_product_jet_left]
    fin_cases i <;> fin_cases j <;> norm_num [Q3SpatialJet.order, Q3SpatialJet.count] <;> ring

/-- In the second argument each coordinate derivative contributes the stationary
minus sign, also for the two mixed Hessian orders. -/
theorem supMean_jet_observation_right (o : Q3SpatialJet) (a b : ℕ) (c : ℝ) (x y : Vec 2) :
    shellObservationApply (supMeanJetObservation o y) (fun z => supMeanProductJet a b c x z) =
      (-c)^o.order * supMeanProductJet (a+o.count 0) (b+o.count 1) c x y := by
  have hf : (fun z => supMeanProductJet a b c x z) =
      (fun z => supMeanProductJet a b (-c) z x) := by
    funext z
    exact (supMean_product_jet_swap a b c x z).symm
  rw [hf, supMean_jet_observation_left, supMean_product_jet_swap]

/-- A constant amplitude commutes with every stored observation derivative. -/
theorem supMean_jet_observation_const_mul (o : Q3SpatialJet) (A : ℝ) (x : Vec 2) (f : Vec 2 → ℝ) :
    shellObservationApply (supMeanJetObservation o x) (fun z => A*f z) =
      A*shellObservationApply (supMeanJetObservation o x) f := by
  cases o with
  | value => rfl
  | first i => exact deriv_const_mul_field A
  | second i j =>
    rw [supMeanJetObservation, supMean_second_observation_apply,
      supMean_second_observation_apply]
    simp only [supMean_coordinate_derivative_const_mul]

end
end ASDExplicitGamma.Gaussian
