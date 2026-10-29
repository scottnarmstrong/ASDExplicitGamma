module

public import ASDExplicitGamma.Main.Q3ValueColumns
public import ASDExplicitGamma.Main.Q3FiniteColumn

/-! Full spatial derivative trace of the actual finite value factor. -/

@[expose] public section
namespace ASDExplicitGamma.Main
open Homogenization ASDExplicitGamma.Gaussian
open scoped BigOperators

theorem mainQ3FiniteValue_fderiv_basis {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (s : Finset ι) (b : ℝ) (L : {l : ℝ // 0 < l}) (x : Vec 2) (k : Fin 2) (j : s) :
    ((fderiv ℝ (mainQ3FiniteValue e s b L) x) (basisVec k)).ofLp j =
      (fderiv ℝ (q3Convolution b L h3Zero (e j)) x) (basisVec k) := by
  rw [mainQ3FiniteValue_fderiv, q3Convolution_fderiv_basis b L h3Zero (by decide)]
  fin_cases k <;> norm_num [Fin.sum_univ_two, basisVec, mainQ3JetIndex, h3Next, h3Zero,
    Model.Q3SpatialJet.count, Pi.single_apply]

/-- The full derivative trace is the column moment31.2, distinct from the
spatial operator norm used in the mean-value step. -/
theorem mainQ3FiniteValue_derivative_frobenius {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (s : Finset ι) (b : ℝ) (L : {l : ℝ // 0 < l}) (x : Vec 2) :
    (∑ k : Fin 2, ‖(fderiv ℝ (mainQ3FiniteValue e s b L) x) (basisVec k)‖^2) ≤
      (156/5)*b^2/L.1^2 := by
  have h := mainQ3FiniteColumn_norm_sq_le e s b L x
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type] at h
  simp_rw [EuclideanSpace.real_norm_sq_eq, mainQ3FiniteValue_fderiv_basis]
  rw [Finset.sum_comm]
  exact h

end ASDExplicitGamma.Main
