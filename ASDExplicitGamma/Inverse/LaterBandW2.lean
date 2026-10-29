module

public import ASDExplicitGamma.Inverse.SmoothW2
public import ASDExplicitGamma.Gaussian.DerivativeLawStored
public import ASDExplicitGamma.Model.Cutoff

/-! The actual finite later-shell scalar band as the genuine W^{2,∞}
perturbation of the coarse-sensitivity theorem. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3 Algsuperdiff.Frozen.Assumptions
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
open scoped Matrix.Norms.Elementwise
noncomputable section

/-- Literal later-shell scalar band, before any spatial averaging or gauge. -/
def laterScalarBand (n J : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) (x : Vec 2) : ℝ :=
  ∑ k ∈ Finset.Ioc n J, weights k*shellScalarValue (ω.val k) x

theorem later_scalar_band_contDiff (n J : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) :
    ContDiff ℝ 2 (laterScalarBand n J weights ω) := by
  apply ContDiff.sum
  intro k _
  exact contDiff_const.mul (shellScalarEntry.contDiff.comp (ω.val k).contDiff_two)

/-- The stored first derivatives of the same actual finite scalar band. -/
def laterScalarFirst (n J : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) (i : Fin 2) (x : Vec 2) : ℝ :=
  ∑ k ∈ Finset.Ioc n J, weights k*shellScalarFirst (basisVec i) (ω.val k) x

theorem later_scalar_band_hasFDerivAt (n J : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) (x : Vec 2) :
    HasFDerivAt (laterScalarBand n J weights ω)
      (∑ k ∈ Finset.Ioc n J, weights k • shellScalarDerivative (ω.val k) x) x := by
  convert HasFDerivAt.sum (u := Finset.Ioc n J)
    (fun k _ => (shellScalarValue_hasFDerivAt (ω.val k) x).const_mul (weights k)) using 1
  funext y
  simp only [laterScalarBand,Finset.sum_apply]

theorem later_scalar_band_derivative (n J : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) (i : Fin 2) :
    smoothScalarDerivative (laterScalarBand n J weights ω) i=laterScalarFirst n J weights ω i := by
  funext x
  unfold smoothScalarDerivative
  rw [(later_scalar_band_hasFDerivAt n J weights ω x).fderiv]
  simp only [sum_apply,smul_apply,smul_eq_mul,laterScalarFirst,shellScalarFirst]

/-- The actual second coordinate derivatives of the actual first coordinate
field, with no arbitrary derivative witness. -/
theorem later_scalar_first_hasFDerivAt (n J : ℤ) (weights : ℤ → ℝ)
    (ω : Cutoff.CutoffSample 2) (i : Fin 2) (x : Vec 2) :
    HasFDerivAt (laterScalarFirst n J weights ω i)
      (∑ k ∈ Finset.Ioc n J, weights k • shellScalarFirstDerivative (basisVec i) (ω.val k) x) x := by
  convert HasFDerivAt.sum (u := Finset.Ioc n J)
    (fun k _ => (shellScalarFirst_hasFDerivAt (basisVec i) (ω.val k) x).const_mul (weights k)) using 1
  funext y
  simp only [laterScalarFirst,Finset.sum_apply]

/-- Canonical W^{2,∞} realization of the actual finite later band. -/
def laterBandW2 (Q : TriadicCube 2) (n J : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) : PlanarW2Infinity Q :=
  smoothW2 Q (laterScalarBand n J weights ω) (later_scalar_band_contDiff n J weights ω)

theorem later_band_w2_value (Q : TriadicCube 2) (n J : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) :
    (laterBandW2 Q n J weights ω).value.toFun=laterScalarBand n J weights ω := rfl

theorem later_band_w2_first (Q : TriadicCube 2) (n J : ℤ) (weights : ℤ → ℝ)
    (ω : Cutoff.CutoffSample 2) (i : Fin 2) :
    ((laterBandW2 Q n J weights ω).gradient.component i).toFun=laterScalarFirst n J weights ω i :=
  later_scalar_band_derivative n J weights ω i

/-- The weak Hessian is exactly the stored second coordinate derivative
sum, in the same index convention as the source Frobenius gate. -/
theorem later_band_w2_second (Q : TriadicCube 2) (n J : ℤ) (weights : ℤ → ℝ)
    (ω : Cutoff.CutoffSample 2) (i j : Fin 2) (x : Vec 2) :
    ((laterBandW2 Q n J weights ω).gradient.component i).grad x j =
      ∑ k ∈ Finset.Ioc n J, weights k*shellScalarFirstDerivative (basisVec i) (ω.val k) x (basisVec j) := by
  change (fderiv ℝ (smoothScalarDerivative (laterScalarBand n J weights ω) i) x) (basisVec j)=_
  rw [later_scalar_band_derivative,(later_scalar_first_hasFDerivAt n J weights ω i x).fderiv]
  simp only [sum_apply,smul_apply,smul_eq_mul]

end
end ASDExplicitGamma.Inverse
