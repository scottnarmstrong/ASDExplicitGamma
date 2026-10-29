module

public import ASDExplicitGamma.Inverse.PureFluxGeneratorCenteredDirections
public import ASDExplicitGamma.Main.Q3ValueDerivatives

/-! The centered q3 value row on a family of vector inputs. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
  ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open scoped BigOperators
noncomputable section

/-- A scalar row contracts the Gaussian coordinate of vector inputs. -/
def pureFluxEuclideanScalarRow {κ ρ : Type*} [Fintype κ] [Fintype ρ]
    (a : EuclideanSpace ℝ κ) :
    EuclideanSpace ℝ (κ × ρ) →L[ℝ] EuclideanSpace ℝ ρ :=
  LinearMap.toContinuousLinearMap {
    toFun c := WithLp.toLp 2 (fun i => ∑ l : κ, a.ofLp l*c.ofLp (l,i))
    map_add' := by intro c d; ext i; simp [mul_add, Finset.sum_add_distrib]
    map_smul' := by intro t c; ext i; simp [Finset.mul_sum, mul_assoc, mul_left_comm] }

theorem pureFluxEuclideanScalarRow_apply {κ ρ : Type*} [Fintype κ] [Fintype ρ]
    (a : EuclideanSpace ℝ κ) (c : EuclideanSpace ℝ (κ × ρ)) (i : ρ) :
    (pureFluxEuclideanScalarRow a c).ofLp i = ∑ l : κ, a.ofLp l*c.ofLp (l,i) := rfl

/-- The value row depends bounded linearly on its coefficient vector. -/
def pureFluxEuclideanScalarRowMap {κ ρ : Type*} [Fintype κ] [Fintype ρ] :
    EuclideanSpace ℝ κ →L[ℝ]
      (EuclideanSpace ℝ (κ × ρ) →L[ℝ] EuclideanSpace ℝ ρ) :=
  LinearMap.toContinuousLinearMap {
    toFun := pureFluxEuclideanScalarRow
    map_add' := by intro a b; ext c i; simp [pureFluxEuclideanScalarRow_apply,
      add_mul, Finset.sum_add_distrib]
    map_smul' := by intro t a; ext c i; simp [pureFluxEuclideanScalarRow_apply,
      Finset.mul_sum, mul_assoc] }

theorem pureFluxEuclideanScalarRowMap_apply {κ ρ : Type*} [Fintype κ] [Fintype ρ]
    (a : EuclideanSpace ℝ κ) (c : EuclideanSpace ℝ (κ × ρ)) (i : ρ) :
    (pureFluxEuclideanScalarRowMap a c).ofLp i = ∑ l : κ, a.ofLp l*c.ofLp (l,i) := rfl

theorem pureFluxEuclideanScalarRow_norm_sq_apply_le {κ ρ : Type*} [Fintype κ] [Fintype ρ]
    (a : EuclideanSpace ℝ κ) (c : EuclideanSpace ℝ (κ × ρ)) :
    ‖pureFluxEuclideanScalarRow a c‖^2 ≤ ‖a‖^2*‖c‖^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [pureFluxEuclideanScalarRow_apply]
  calc
    _ ≤ ∑ i : ρ, (∑ l : κ, a.ofLp l^2)*(∑ l : κ, c.ofLp (l,i)^2) :=
      Finset.sum_le_sum fun i _ => Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
    _ = _ := by
      rw [← Finset.mul_sum, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
        Fintype.sum_prod_type, Finset.sum_comm]

theorem pureFluxEuclideanScalarRow_norm_le {κ ρ : Type*} [Fintype κ] [Fintype ρ]
    (a : EuclideanSpace ℝ κ) : ‖pureFluxEuclideanScalarRow (ρ := ρ) a‖ ≤ ‖a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a)
  intro c
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg a) (norm_nonneg c))).mp
  rw [mul_pow]
  exact pureFluxEuclideanScalarRow_norm_sq_apply_le a c

/-- The actual centered q3 scalar row on Gaussian-indexed planar vectors. -/
def pureFluxQ3CenteredValueRow {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (s : Finset ι) (b : ℝ) (L : {l : ℝ // 0 < l}) (Q U : TriadicCube 2) :
    HilbertOperatorW1Infinity U (EuclideanSpace ℝ (s × Fin 2)) (EuclideanSpace ℝ (Fin 2)) :=
  mainSmoothHilbertOperator U
    (fun x => pureFluxEuclideanScalarRowMap
      (mainQ3FiniteValue e s b L x-mainQ3FiniteValue e s b L (cubeCenter Q)))
    ((pureFluxEuclideanScalarRowMap (κ := s) (ρ := Fin 2)).contDiff.comp
      ((mainQ3FiniteValue_contDiff e s b L).sub contDiff_const))

theorem pureFluxQ3CenteredValueRow_apply {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (s : Finset ι) (b : ℝ) (L : {l : ℝ // 0 < l}) (Q U : TriadicCube 2)
    (x : Vec 2) (c : EuclideanSpace ℝ (s × Fin 2)) (i : Fin 2) :
    ((pureFluxQ3CenteredValueRow e s b L Q U).toFun x c).ofLp i =
      ∑ l : s, (q3Convolution b L h3Zero (e l) x -
        q3Convolution b L h3Zero (e l) (cubeCenter Q))*c.ofLp (l,i) := by
  change (pureFluxEuclideanScalarRowMap _ c).ofLp i = _
  simp [pureFluxEuclideanScalarRowMap_apply, mainQ3FiniteValue, PiLp.sub_apply,
    sub_mul, Finset.sum_sub_distrib]

theorem pureFluxQ3CenteredValueRow_grad_apply {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (s : Finset ι) (b : ℝ) (L : {l : ℝ // 0 < l}) (Q U : TriadicCube 2)
    (x : Vec 2) (c : EuclideanSpace ℝ (s × Fin 2)) (i j : Fin 2) :
    ((pureFluxQ3CenteredValueRow e s b L Q U).grad x j c).ofLp i =
      ∑ l : s, q3Convolution b L (mainQ3JetIndex (.first j)) (e l) x*c.ofLp (l,i) := by
  let T := pureFluxEuclideanScalarRowMap (κ := s) (ρ := Fin 2)
  let ψ := fun x => mainQ3FiniteValue e s b L x-mainQ3FiniteValue e s b L (cubeCenter Q)
  have hψ : ContDiff ℝ 1 ψ := (mainQ3FiniteValue_contDiff e s b L).sub contDiff_const
  have h := T.hasFDerivAt.comp x
    (hψ.differentiable (by norm_num)).differentiableAt.hasFDerivAt
  have he := congrArg (fun D => D (basisVec j)) h.fderiv
  dsimp only [Function.comp_def, ContinuousLinearMap.comp_apply] at he
  change (((fderiv ℝ (fun y => T (ψ y)) x) (basisVec j)) c).ofLp i = _
  rw [he, pureFluxEuclideanScalarRowMap_apply]
  simp only [ψ, fderiv_sub_const]
  simp_rw [mainQ3FiniteValue_fderiv_basis]
  apply Finset.sum_congr rfl
  intro l hl
  rw [q3Convolution_fderiv_basis b L h3Zero (by decide)]
  congr 2
  fin_cases j <;> rfl

/-- Centered value covariance has the exact parent-radius cap. -/
theorem pureFluxQ3CenteredValueRow_norm_le {ι : Type*}
    (e : HilbertBasis ι ℝ WhiteNoise) (s : Finset ι) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (Q U : TriadicCube 2) {x : Vec 2} (hx : x ∈ cubeSet Q) :
    ‖(pureFluxQ3CenteredValueRow e s b L Q U).toFun x‖ ≤
      Real.sqrt (b^2*((78/5:ℝ)/2)*(cubeScaleFactor Q/L.1)^2) := by
  apply (pureFluxEuclideanScalarRow_norm_le _).trans
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (by positivity : 0 ≤ b^2*((78/5:ℝ)/2)*(cubeScaleFactor Q/L.1)^2)]
  exact pureFluxQ3CenteredFiniteValue_norm_sq_le e s b L Q hx

/-- The value row's combined derivative uses the first covariance operator moment. -/
theorem pureFluxQ3CenteredValueRow_combined_gradient_le {ι : Type*}
    (e : HilbertBasis ι ℝ WhiteNoise) (s : Finset ι) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (Q U : TriadicCube 2) (x : Vec 2)
    (c : EuclideanSpace ℝ (s × Fin 2)) :
    (∑ j : Fin 2, ‖(pureFluxQ3CenteredValueRow e s b L Q U).grad x j c‖^2) ≤
      ((78/5)*b^2/L.1^2)*‖c‖^2 := by
  have hper (i : Fin 2) :
      (∑ j : Fin 2, (∑ l : s,
        q3Convolution b L (mainQ3JetIndex (.first j)) (e l) x*c.ofLp (l,i))^2) ≤
      ((78/5)*b^2/L.1^2)*(∑ l : s, c.ofLp (l,i)^2) := by
    let ci : EuclideanSpace ℝ s := WithLp.toLp 2 (fun l => c.ofLp (l,i))
    have h := pureFluxQ3DerivativeRow_norm_sq_apply_le e s b L Q x ci
    simpa only [EuclideanSpace.real_norm_sq_eq, pureFluxQ3DerivativeRow_apply, ci,
      WithLp.ofLp_toLp, mul_comm] using h
  simp only [EuclideanSpace.real_norm_sq_eq, pureFluxQ3CenteredValueRow_grad_apply]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ i : Fin 2, ((78/5)*b^2/L.1^2)*(∑ l : s, c.ofLp (l,i)^2) :=
      Finset.sum_le_sum fun i _ => hper i
    _ = _ := by rw [← Finset.mul_sum, Fintype.sum_prod_type, Finset.sum_comm]

end
end ASDExplicitGamma.Inverse
