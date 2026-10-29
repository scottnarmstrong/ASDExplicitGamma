module

public import ASDExplicitGamma.Inverse.PureFluxGeneratorOperatorProduct
public import ASDExplicitGamma.Main.Q3FiniteColumn
public import ASDExplicitGamma.Main.Q3RowProduct
public import ASDExplicitGamma.Main.SmoothHilbertOperator

/-! Finite covariance row operators with their actual combined derivatives. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
  ASDExplicitGamma.Triadic ASDExplicitGamma.Variational ASDExplicitGamma.Model
open scoped BigOperators
noncomputable section

/-- Contract the Gaussian coordinate of a finite matrix column. -/
def pureFluxEuclideanRow {κ ρ : Type*} [Fintype κ] [Fintype ρ]
    (a : EuclideanSpace ℝ (κ × ρ)) :
    EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ ρ :=
  ∑ l : κ, (PiLp.proj 2 (fun _ : κ => ℝ) l).smulRight
    (WithLp.toLp 2 (fun i => a.ofLp (l,i)))

theorem pureFluxEuclideanRow_apply {κ ρ : Type*} [Fintype κ] [Fintype ρ]
    (a : EuclideanSpace ℝ (κ × ρ)) (c : EuclideanSpace ℝ κ) (i : ρ) :
    (pureFluxEuclideanRow a c).ofLp i = ∑ l : κ, c.ofLp l * a.ofLp (l,i) := by
  simp [pureFluxEuclideanRow, ContinuousLinearMap.sum_apply, Finset.sum_apply,
    ContinuousLinearMap.smulRight_apply, PiLp.proj_apply]

/-- The contraction depends bounded linearly on the finite matrix column. -/
def pureFluxEuclideanRowMap {κ ρ : Type*} [Fintype κ] [Fintype ρ] :
    EuclideanSpace ℝ (κ × ρ) →L[ℝ]
      (EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ ρ) :=
  LinearMap.toContinuousLinearMap {
    toFun := pureFluxEuclideanRow
    map_add' := by
      intro a b
      ext c i
      simp [pureFluxEuclideanRow_apply, mul_add, Finset.sum_add_distrib]
    map_smul' := by
      intro t a
      ext c i
      simp [pureFluxEuclideanRow_apply, Finset.mul_sum, mul_left_comm, mul_comm,
        mul_assoc] }

theorem pureFluxEuclideanRowMap_apply {κ ρ : Type*} [Fintype κ] [Fintype ρ]
    (a : EuclideanSpace ℝ (κ × ρ)) (c : EuclideanSpace ℝ κ) (i : ρ) :
    (pureFluxEuclideanRowMap a c).ofLp i = ∑ l : κ, c.ofLp l * a.ofLp (l,i) :=
  pureFluxEuclideanRow_apply a c i

/-- The actual q3 derivative row as a smooth operator field. -/
def pureFluxQ3DerivativeRow {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (s : Finset ι) (b : ℝ) (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2) :
    HilbertOperatorW1Infinity Q (EuclideanSpace ℝ s) (EuclideanSpace ℝ (Fin 2)) :=
  mainSmoothHilbertOperator Q
    (fun x => pureFluxEuclideanRowMap (mainQ3FiniteColumn e s b L x))
    ((pureFluxEuclideanRowMap (κ := s) (ρ := Fin 2)).contDiff.comp
      (mainQ3FiniteColumn_contDiff e s b L))

theorem pureFluxQ3DerivativeRow_apply {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (s : Finset ι) (b : ℝ) (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2)
    (x : Vec 2) (c : EuclideanSpace ℝ s) (i : Fin 2) :
    ((pureFluxQ3DerivativeRow e s b L Q).toFun x c).ofLp i =
      ∑ l : s, c.ofLp l * q3Convolution b L (mainQ3JetIndex (.first i)) (e l) x := by
  change (pureFluxEuclideanRowMap (mainQ3FiniteColumn e s b L x) c).ofLp i = _
  rw [pureFluxEuclideanRowMap_apply]
  apply Finset.sum_congr rfl
  intro l hl
  simp only [mainQ3FiniteColumn, WithLp.ofLp_toLp]
  rw [q3Convolution_fderiv_basis b L h3Zero (by decide)]
  congr 2
  fin_cases i <;> rfl

theorem pureFluxQ3DerivativeRow_grad_apply {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (s : Finset ι) (b : ℝ) (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2)
    (x : Vec 2) (c : EuclideanSpace ℝ s) (i j : Fin 2) :
    ((pureFluxQ3DerivativeRow e s b L Q).grad x j c).ofLp i =
      ∑ l : s, c.ofLp l *
        q3Convolution b L (mainQ3JetIndex (.second i j)) (e l) x := by
  let T := pureFluxEuclideanRowMap (κ := s) (ρ := Fin 2)
  have h := T.hasFDerivAt.comp x
    ((mainQ3FiniteColumn_contDiff e s b L).differentiable (by norm_num)).differentiableAt.hasFDerivAt
  have he := congrArg (fun D => D (basisVec j)) h.fderiv
  dsimp only [Function.comp_def, ContinuousLinearMap.comp_apply] at he
  change (((fderiv ℝ (fun y => T (mainQ3FiniteColumn e s b L y)) x)
    (basisVec j)) c).ofLp i = _
  rw [he, pureFluxEuclideanRowMap_apply]
  apply Finset.sum_congr rfl
  intro l hl
  rw [mainQ3FiniteColumn_fderiv_apply, main_q3_second_coordinate]
  congr 2
  fin_cases i <;> fin_cases j <;> rfl


private def pureFluxRowCoefficients {ι : Type*} (s : Finset ι)
    (c : EuclideanSpace ℝ s) (l : ι) : ℝ := by
  classical
  exact if h : l ∈ s then c.ofLp ⟨l,h⟩ else 0

private theorem pureFluxRowCoefficients_sum {ι : Type*} (s : Finset ι)
    (c : EuclideanSpace ℝ s) (f : ι → ℝ) :
    (∑ l ∈ s, pureFluxRowCoefficients s c l * f l) =
      ∑ l : s, c.ofLp l * f l := by
  rw [← Finset.sum_coe_sort s]
  simp [pureFluxRowCoefficients]

private theorem pureFluxRowCoefficients_sq_sum {ι : Type*} (s : Finset ι)
    (c : EuclideanSpace ℝ s) :
    (∑ l ∈ s, pureFluxRowCoefficients s c l ^ 2) = ‖c‖^2 := by
  rw [← Finset.sum_coe_sort s, EuclideanSpace.real_norm_sq_eq]
  simp [pureFluxRowCoefficients]

/-- The covariance row value uses the sharp first-jet eigenvalue. -/
theorem pureFluxQ3DerivativeRow_norm_sq_apply_le {ι : Type*}
    (e : HilbertBasis ι ℝ WhiteNoise) (s : Finset ι) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2) (x : Vec 2)
    (c : EuclideanSpace ℝ s) :
    ‖(pureFluxQ3DerivativeRow e s b L Q).toFun x c‖^2 ≤
      ((78/5)*b^2/L.1^2)*‖c‖^2 := by
  have h := main_q3_first_row_bound e s (pureFluxRowCoefficients s c) b L x
  simp only [pureFluxRowCoefficients_sum, pureFluxRowCoefficients_sq_sum] at h
  simpa only [EuclideanSpace.real_norm_sq_eq, pureFluxQ3DerivativeRow_apply] using h

/-- The combined derivative retains the sharp Hessian row eigenvalue. -/
theorem pureFluxQ3DerivativeRow_combined_gradient_le {ι : Type*}
    (e : HilbertBasis ι ℝ WhiteNoise) (s : Finset ι) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2) (x : Vec 2)
    (c : EuclideanSpace ℝ s) :
    (∑ j : Fin 2, ‖(pureFluxQ3DerivativeRow e s b L Q).grad x j c‖^2) ≤
      ((23244/25)*b^2/L.1^4)*‖c‖^2 := by
  have h := main_q3_second_row_bound e s (pureFluxRowCoefficients s c) b L x
  simp only [pureFluxRowCoefficients_sum, pureFluxRowCoefficients_sq_sum,
    Fintype.sum_prod_type] at h
  simp only [EuclideanSpace.real_norm_sq_eq, pureFluxQ3DerivativeRow_grad_apply]
  rw [Finset.sum_comm]
  simpa only [EuclideanSpace.real_norm_sq_eq] using h

/-- The actual finite derivative row is bounded as an operator. -/
theorem pureFluxQ3DerivativeRow_norm_le {ι : Type*}
    (e : HilbertBasis ι ℝ WhiteNoise) (s : Finset ι) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (Q : TriadicCube 2) (x : Vec 2) :
    ‖(pureFluxQ3DerivativeRow e s b L Q).toFun x‖ ≤
      Real.sqrt ((78/5)*b^2/L.1^2) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro c
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg c))).mp
  rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (78/5:ℝ)*b^2/L.1^2)]
  exact pureFluxQ3DerivativeRow_norm_sq_apply_le e s b L Q x c

end
end ASDExplicitGamma.Inverse
