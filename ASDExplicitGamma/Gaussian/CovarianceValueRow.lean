module

public import ASDExplicitGamma.Inverse.PureFluxGeneratorValueRow
public import ASDExplicitGamma.Gaussian.GeneratorBounds

/-! The full q3 covariance value row, retaining its common-input operator bound. -/

@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization MeasureTheory ASDExplicitGamma.Main ASDExplicitGamma.Inverse
  ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open scoped BigOperators
noncomputable section

/-- The full q3 scalar row on Gaussian-indexed planar vectors. -/
def q3ValueRow {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (s : Finset ι) (b : ℝ) (L : {l : ℝ // 0 < l}) (U : TriadicCube 2) :
    HilbertOperatorW1Infinity U (EuclideanSpace ℝ (s × Fin 2)) (EuclideanSpace ℝ (Fin 2)) :=
  mainSmoothHilbertOperator U
    (fun x => pureFluxEuclideanScalarRowMap
      (mainQ3FiniteValue e s b L x))
    ((pureFluxEuclideanScalarRowMap (κ := s) (ρ := Fin 2)).contDiff.comp
      (mainQ3FiniteValue_contDiff e s b L))

theorem q3ValueRow_apply {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (s : Finset ι) (b : ℝ) (L : {l : ℝ // 0 < l}) (U : TriadicCube 2)
    (x : Vec 2) (c : EuclideanSpace ℝ (s × Fin 2)) (i : Fin 2) :
    ((q3ValueRow e s b L U).toFun x c).ofLp i =
      ∑ l : s, q3Convolution b L h3Zero (e l) x*c.ofLp (l,i) := by
  change (pureFluxEuclideanScalarRowMap _ c).ofLp i = _
  simp [pureFluxEuclideanScalarRowMap_apply, mainQ3FiniteValue]

theorem q3ValueRow_grad_apply {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (s : Finset ι) (b : ℝ) (L : {l : ℝ // 0 < l}) (U : TriadicCube 2)
    (x : Vec 2) (c : EuclideanSpace ℝ (s × Fin 2)) (i j : Fin 2) :
    ((q3ValueRow e s b L U).grad x j c).ofLp i =
      ∑ l : s, q3Convolution b L (mainQ3JetIndex (.first j)) (e l) x*c.ofLp (l,i) := by
  let T := pureFluxEuclideanScalarRowMap (κ := s) (ρ := Fin 2)
  let ψ := mainQ3FiniteValue e s b L
  have hψ : ContDiff ℝ 1 ψ := mainQ3FiniteValue_contDiff e s b L
  have h := T.hasFDerivAt.comp x
    (hψ.differentiable (by norm_num)).differentiableAt.hasFDerivAt
  have he := congrArg (fun D => D (basisVec j)) h.fderiv
  dsimp only [Function.comp_def, ContinuousLinearMap.comp_apply] at he
  change (((fderiv ℝ (fun y => T (ψ y)) x) (basisVec j)) c).ofLp i = _
  rw [he, pureFluxEuclideanScalarRowMap_apply]
  dsimp only [ψ]
  simp_rw [mainQ3FiniteValue_fderiv_basis]
  apply Finset.sum_congr rfl
  intro l hl
  rw [q3Convolution_fderiv_basis b L h3Zero (by decide)]
  congr 2
  fin_cases j <;> rfl

/-- The full value row is bounded by the physical shell amplitude. -/
theorem q3ValueRow_norm_le {ι : Type*}
    (e : HilbertBasis ι ℝ WhiteNoise) (s : Finset ι) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (U : TriadicCube 2) (x : Vec 2) :
    ‖(q3ValueRow e s b L U).toFun x‖ ≤ Real.sqrt (b^2) := by
  apply (pureFluxEuclideanScalarRow_norm_le _).trans
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (sq_nonneg b)]
  exact main_q3_finite_value_norm_sq_le e s b L x

/-- The value row's combined derivative uses the first covariance operator moment. -/
theorem q3ValueRow_combined_gradient_le {ι : Type*}
    (e : HilbertBasis ι ℝ WhiteNoise) (s : Finset ι) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (U : TriadicCube 2) (x : Vec 2)
    (c : EuclideanSpace ℝ (s × Fin 2)) :
    (∑ j : Fin 2, ‖(q3ValueRow e s b L U).grad x j c‖^2) ≤
      ((78/5)*b^2/L.1^2)*‖c‖^2 := by
  have hper (i : Fin 2) :
      (∑ j : Fin 2, (∑ l : s,
        q3Convolution b L (mainQ3JetIndex (.first j)) (e l) x*c.ofLp (l,i))^2) ≤
      ((78/5)*b^2/L.1^2)*(∑ l : s, c.ofLp (l,i)^2) := by
    let ci : EuclideanSpace ℝ s := WithLp.toLp 2 (fun l => c.ofLp (l,i))
    have h := pureFluxQ3DerivativeRow_norm_sq_apply_le e s b L U x ci
    simpa only [EuclideanSpace.real_norm_sq_eq, pureFluxQ3DerivativeRow_apply, ci,
      WithLp.ofLp_toLp, mul_comm] using h
  simp only [EuclideanSpace.real_norm_sq_eq, q3ValueRow_grad_apply]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ i : Fin 2, ((78/5)*b^2/L.1^2)*(∑ l : s, c.ofLp (l,i)^2) :=
      Finset.sum_le_sum fun i _ => hper i
    _ = _ := by rw [← Finset.mul_sum, Fintype.sum_prod_type, Finset.sum_comm]

end
end ASDExplicitGamma.Gaussian
