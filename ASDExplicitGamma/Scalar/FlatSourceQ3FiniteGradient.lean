module

public import ASDExplicitGamma.Scalar.FlatSourceQ3FiniteH1
public import ASDExplicitGamma.Gaussian.Q3H3Series
public import ASDExplicitGamma.Gaussian.Q3SeriesCovariance
public import ASDExplicitGamma.Gaussian.Q3H3Range
public import ASDExplicitGamma.Gaussian.C1JetLimit
public import ASDExplicitGamma.Scalar.FlatSourceProjectedModeTrace
public import ASDExplicitGamma.Scalar.FlatSourceQ3SpatialWick
public import ASDExplicitGamma.Scalar.FlatSourcePoincare
public import ASDExplicitGamma.Gaussian.Q3SobolevOperator

/-! Finite q3 source products retain their common-noise weak gradient. -/

@[expose] public section

open MeasureTheory Homogenization
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
open ASDExplicitGamma.Response ASDExplicitGamma.Main
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped ENNReal Topology RealInnerProductSpace

namespace ASDExplicitGamma.Scalar

private theorem enumerated_h1_apply
    {U : Set (Vec 2)} (F : whiteBasisIndex → H1Function U)
    (n : ℕ) (x : Vec 2) :
    (gaussEnumerated F n) x = gaussEnumerated (fun q => F q x) n := by
  classical
  let := Encodable.ofCountable whiteBasisIndex
  by_cases hn : n ∈ Set.range (Encodable.encode : whiteBasisIndex → ℕ)
  · obtain ⟨q, rfl⟩ := hn
    rw [enumerated_encode, enumerated_encode]
  · rw [gaussEnumerated, gaussEnumerated,
      Function.extend_apply' _ _ _ hn, Function.extend_apply' _ _ _ hn]
    rfl

private theorem enumerated_h1_grad_apply
    {U : Set (Vec 2)} (F : whiteBasisIndex → H1Function U)
    (n : ℕ) (x : Vec 2) (i : Fin 2) :
    (gaussEnumerated F n).grad x i =
      gaussEnumerated (fun q => (F q).grad x i) n := by
  classical
  let := Encodable.ofCountable whiteBasisIndex
  by_cases hn : n ∈ Set.range (Encodable.encode : whiteBasisIndex → ℕ)
  · obtain ⟨q, rfl⟩ := hn
    rw [enumerated_encode, enumerated_encode]
  · rw [gaussEnumerated, gaussEnumerated,
      Function.extend_apply' _ _ _ hn, Function.extend_apply' _ _ _ hn]
    rfl

private theorem enumerated_fun_apply'
    {ι : Type*} [Countable ι] (F : ι → Vec 2 → ℝ)
    (n : ℕ) (x : Vec 2) :
    gaussEnumerated F n x = gaussEnumerated (fun q => F q x) n := by
  classical
  let := Encodable.ofCountable ι
  by_cases hn : n ∈ Set.range (Encodable.encode : ι → ℕ)
  · obtain ⟨q, rfl⟩ := hn
    rw [enumerated_encode, enumerated_encode]
  · rw [gaussEnumerated, gaussEnumerated,
      Function.extend_apply' _ _ _ hn, Function.extend_apply' _ _ _ hn]
    rfl

private theorem h1_sum_smul_value
    {U : Set (Vec 2)} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (c : ι → ℝ) (u : ι → H1Function U) (x : Vec 2) :
    (∑ n ∈ s, c n • u n).toFun x = ∑ n ∈ s, c n * u n x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp [Finset.sum_insert, ha, ih]

private theorem h1_sum_smul_gradient
    {U : Set (Vec 2)} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (c : ι → ℝ) (u : ι → H1Function U)
    (x : Vec 2) (i : Fin 2) :
    (∑ n ∈ s, c n • u n).grad x i = ∑ n ∈ s, c n * (u n).grad x i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp [Finset.sum_insert, ha, ih]

/-- The scalar coefficients used by the finite q3 source. -/
noncomputable def flatSourceQ3FiniteValueMode
    (β : ℝ) (L : {l : ℝ // 0 < l}) (n : ℕ) (x : Vec 2) : ℝ :=
  q3Convolution β L h3Zero (gaussEnumerated whiteBasis n) x

/-- The spatial derivative coefficients of the finite q3 scalar. -/
noncomputable def flatSourceQ3FiniteValueDerivativeMode
    (β : ℝ) (L : {l : ℝ // 0 < l}) (i : Fin 2) (n : ℕ) (x : Vec 2) : ℝ :=
  (fderiv ℝ (q3Convolution β L h3Zero
    (gaussEnumerated whiteBasis n)) x) (basisVec i)

noncomputable def flatSourceQ3DerivativeIndex (i : Fin 2) : H3Index :=
  h3Next h3Zero i (by
    fin_cases i <;> norm_num [h3Zero, H3Index])

/-- The clamped scalar modes used to state global pointwise variance bounds. -/
noncomputable def flatSourceQ3FiniteClampedValueMode
    {a b c d : ℝ} (β : ℝ) (L : {l : ℝ // 0 < l})
    (hab : a < b) (hcd : c < d) (n : ℕ) (x : Vec 2) : ℝ :=
  q3Convolution β L h3Zero (gaussEnumerated whiteBasis n)
    (lambda8CovarianceClamp a b c d hab hcd x).1

/-- The clamped derivative modes use the same zero-padded Gaussian coordinates. -/
noncomputable def flatSourceQ3FiniteClampedDerivativeMode
    {a b c d : ℝ} (β : ℝ) (L : {l : ℝ // 0 < l})
    (hab : a < b) (hcd : c < d) (i : Fin 2) (n : ℕ) (x : Vec 2) : ℝ :=
  q3Convolution β L (flatSourceQ3DerivativeIndex i)
    (gaussEnumerated whiteBasis n)
    (lambda8CovarianceClamp a b c d hab hcd x).1

private theorem enumerated_convolution_coeff
    {β : ℝ} (L : {l : ℝ // 0 < l})
    (k : H3Index) (x : Vec 2) (n : ℕ) :
    q3Convolution β L k (gaussEnumerated whiteBasis n) x =
      gaussEnumerated (fun q : whiteBasisIndex =>
        q3Convolution β L k (whiteBasis q) x) n := by
  classical
  let := Encodable.ofCountable whiteBasisIndex
  by_cases hn : n ∈ Set.range (Encodable.encode : whiteBasisIndex → ℕ)
  · obtain ⟨q, rfl⟩ := hn
    rw [enumerated_encode, enumerated_encode]
  · rw [gaussEnumerated, gaussEnumerated,
      Function.extend_apply' _ _ _ hn, Function.extend_apply' _ _ _ hn]
    simp [q3Convolution]

/-- The common q3 value and its two first-derivative families have uniform
finite-mode variance caps, valid at every point after clamping. -/
theorem flat_source_q3_clamped_finite_variance_caps
    {a b c d β : ℝ} (hab : a < b) (hcd : c < d)
    (L : {l : ℝ // 0 < l}) (N : ℕ) (x : Vec 2) :
    (∑ n ∈ Finset.range N,
      (flatSourceQ3FiniteClampedValueMode β L hab hcd n x) ^ 2 ≤ β ^ 2) ∧
    (∑ i : Fin 2, ∑ n ∈ Finset.range N,
      (flatSourceQ3FiniteClampedDerivativeMode β L hab hcd i n x) ^ 2 ≤
        β ^ 2 / L.1 ^ 2 * (156 / 5 : ℝ)) := by
  classical
  let xRect := lambda8CovarianceClamp a b c d hab hcd x
  let coeff : whiteBasisIndex → ℝ := fun q =>
    q3Convolution β L h3Zero (whiteBasis q) xRect.1
  have hcoeff : Summable (fun q => coeff q ^ 2) := by
    simpa only [coeff, q3Convolution] using
      hilbertBasis_summable_sq whiteBasis
        (q3Section β L h3Zero xRect.1)
  have hcoeffNorm : Summable (fun q => ‖coeff q‖ ^ 2) := by
    simpa only [Real.norm_eq_abs, sq_abs] using hcoeff
  have henum : Summable (fun n => ‖gaussEnumerated coeff n‖ ^ 2) :=
    enumerated_summable_sq coeff hcoeffNorm
  have hvalueEq (n : ℕ) :
      flatSourceQ3FiniteClampedValueMode β L hab hcd n x =
        gaussEnumerated coeff n := by
    simpa [flatSourceQ3FiniteClampedValueMode, coeff, xRect] using
      enumerated_convolution_coeff L h3Zero xRect.1 n
  have hvalue :
      ∑ n ∈ Finset.range N,
        (flatSourceQ3FiniteClampedValueMode β L hab hcd n x) ^ 2 ≤ β ^ 2 := by
    calc
      _ = ∑ n ∈ Finset.range N, ‖gaussEnumerated coeff n‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [hvalueEq n, Real.norm_eq_abs, sq_abs]
      _ ≤ ∑' n, ‖gaussEnumerated coeff n‖ ^ 2 := by
        apply henum.sum_le_tsum (Finset.range N)
        intro n hn
        exact sq_nonneg _
      _ = ‖q3Section β L h3Zero xRect.1‖ ^ 2 := by
        calc
          _ = ∑' n, (gaussEnumerated coeff n) ^ 2 := by
            apply tsum_congr
            intro n
            rw [Real.norm_eq_abs, sq_abs]
          _ = ∑' q : whiteBasisIndex,
              (q3Convolution β L h3Zero (whiteBasis q) xRect.1) ^ 2 := by
            rw [show (fun n => (gaussEnumerated coeff n) ^ 2) =
              fun n => (q3Convolution β L h3Zero
                (gaussEnumerated whiteBasis n) xRect.1) ^ 2 by
                funext n
                rw [← enumerated_convolution_coeff L h3Zero
                  xRect.1 n]]
            simpa [coeff, q3Convolution] using
              (enumerated_tsum_apply whiteBasis
                (fun u : WhiteNoise =>
                  ⟪u, q3Section β L h3Zero xRect.1⟫ ^ 2) (by simp))
          _ = _ := by
            simpa [coeff, q3Convolution] using
              hilbertBasis_norm_sq whiteBasis
                (q3Section β L h3Zero xRect.1)
      _ = β ^ 2 := by
        rw [gaussQ3Section_norm_sq]
        norm_num [h3Zero, H3Index, q3DerivativeMoment]
        field_simp [ne_of_gt L.2]
  have hsection (i : Fin 2) :
      ‖q3Section β L (flatSourceQ3DerivativeIndex i) xRect.1‖ ^ 2 =
        β ^ 2 / L.1 ^ 2 * (78 / 5 : ℝ) := by
    rw [gaussQ3Section_norm_sq]
    fin_cases i <;>
      norm_num [flatSourceQ3DerivativeIndex, h3Next,
        h3Zero, H3Index, q3DerivativeMoment] <;>
      field_simp [ne_of_gt L.2]
  have hderiv (i : Fin 2) :
      ∑ n ∈ Finset.range N,
        (flatSourceQ3FiniteClampedDerivativeMode β L hab hcd i n x) ^ 2 ≤
        β ^ 2 / L.1 ^ 2 * (78 / 5 : ℝ) := by
    let k := flatSourceQ3DerivativeIndex i
    let coeff : whiteBasisIndex → ℝ := fun q =>
      q3Convolution β L k (whiteBasis q) xRect.1
    have hcoeff : Summable (fun q => coeff q ^ 2) := by
      simpa only [coeff, q3Convolution] using
        hilbertBasis_summable_sq whiteBasis (q3Section β L k xRect.1)
    have hcoeffNorm : Summable (fun q => ‖coeff q‖ ^ 2) := by
      simpa only [Real.norm_eq_abs, sq_abs] using hcoeff
    have henum : Summable (fun n => ‖gaussEnumerated coeff n‖ ^ 2) :=
      enumerated_summable_sq coeff hcoeffNorm
    have heq (n : ℕ) :
        flatSourceQ3FiniteClampedDerivativeMode β L hab hcd i n x =
          gaussEnumerated coeff n := by
      simpa [flatSourceQ3FiniteClampedDerivativeMode, coeff, k, xRect] using
        enumerated_convolution_coeff L k xRect.1 n
    have hparseval :
        (∑' n : ℕ, ‖gaussEnumerated coeff n‖ ^ 2) =
          ‖q3Section β L k xRect.1‖ ^ 2 := by
      calc
        (∑' n : ℕ, ‖gaussEnumerated coeff n‖ ^ 2) =
            ∑' n : ℕ, (gaussEnumerated coeff n) ^ 2 := by
          apply tsum_congr
          intro n
          rw [Real.norm_eq_abs, sq_abs]
        _ = ∑' q : whiteBasisIndex,
            (q3Convolution β L k (whiteBasis q) xRect.1) ^ 2 := by
          rw [show (fun n => (gaussEnumerated coeff n) ^ 2) =
            fun n => (q3Convolution β L k
              (gaussEnumerated whiteBasis n) xRect.1) ^ 2 by
              funext n
              rw [← enumerated_convolution_coeff L k xRect.1 n]]
          simpa [coeff, q3Convolution] using
            (enumerated_tsum_apply whiteBasis
              (fun u : WhiteNoise =>
                ⟪u, q3Section β L k xRect.1⟫ ^ 2) (by simp))
        _ = ‖q3Section β L k xRect.1‖ ^ 2 := by
          simpa [coeff, q3Convolution] using
            hilbertBasis_norm_sq whiteBasis
              (q3Section β L k xRect.1)
    calc
      _ = ∑ n ∈ Finset.range N, ‖gaussEnumerated coeff n‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [heq n, Real.norm_eq_abs, sq_abs]
      _ ≤ ∑' n, ‖gaussEnumerated coeff n‖ ^ 2 := by
        apply henum.sum_le_tsum (Finset.range N)
        intro n hn
        exact sq_nonneg _
      _ = β ^ 2 / L.1 ^ 2 * (78 / 5 : ℝ) :=
        hparseval.trans (by simpa [k] using hsection i)
  refine ⟨hvalue, ?_⟩
  rw [Fin.sum_univ_two]
  calc
    _ ≤ β ^ 2 / L.1 ^ 2 * (78 / 5 : ℝ) +
        β ^ 2 / L.1 ^ 2 * (78 / 5 : ℝ) :=
      add_le_add (hderiv 0) (hderiv 1)
    _ = β ^ 2 / L.1 ^ 2 * (156 / 5 : ℝ) := by ring

/-- The parent-projection value modes in the same zero-padded coordinates. -/
noncomputable def flatSourceQ3FiniteProjectedMode
    (Q : TriadicCube 2) (β : ℝ) (L : {l : ℝ // 0 < l})
    (e : Vec 2) (i : Fin 2) (n : ℕ) (x : Vec 2) : ℝ :=
  gaussEnumerated (fun j : whiteBasisIndex => fun y : Vec 2 =>
    (lambda8Q3GaussianModeParentPotential Q β L
      (matVecMul responsePlanarJ e) j).toH1Function.grad y i) n x

/-- The parent-projection weak-gradient modes are its actual Hessian modes. -/
noncomputable def flatSourceQ3FiniteProjectedGradientMode
    (Q : TriadicCube 2) (β : ℝ) (L : {l : ℝ // 0 < l})
    (e : Vec 2) (i j : Fin 2) (n : ℕ) (x : Vec 2) : ℝ :=
  gaussEnumerated (fun q : whiteBasisIndex =>
    (lambda8Q3GaussianModeParentHessian Q β L
      (matVecMul responsePlanarJ e) q).hess i j) n x

theorem flat_source_q3_finite_projected_component_value
    (Q : TriadicCube 2) (β : ℝ) (L : {l : ℝ // 0 < l})
    (e : Vec 2) (N : ℕ) (ω : ℕ → ℝ) (i : Fin 2) (x : Vec 2) :
    flatSourceQ3FiniteProjectedComponent Q β L e N ω i x =
      gaussianScalarPartialSum
        (fun n => flatSourceQ3FiniteProjectedMode Q β L e i n x) N ω := by
  rw [flatSourceQ3FiniteProjectedComponent]
  rw [h1_sum_smul_value]
  unfold gaussianScalarPartialSum flatSourceQ3FiniteProjectedMode
  apply Finset.sum_congr rfl
  intro n hn
  let F : whiteBasisIndex → H1Function (openCubeSet Q) := fun q =>
    (lambda8Q3GaussianModeParentHessian Q β L
      (matVecMul responsePlanarJ e) q).gradCoordH1Function i
  let G : whiteBasisIndex → Vec 2 → ℝ := fun q y =>
    (lambda8Q3GaussianModeParentPotential Q β L
      (matVecMul responsePlanarJ e) q).toH1Function.grad y i
  have hcoord : (fun q => (F q).toFun x) = fun q => G q x := by
    funext q
    exact Homogenization.HasWeakHessianOn.gradCoordH1Function_apply _ _ _
  have hF := enumerated_h1_apply (F := F) n x
  rw [hcoord] at hF
  have hG := enumerated_fun_apply' G n x
  change ω n * (gaussEnumerated F n).toFun x = ω n * (gaussEnumerated G n) x
  calc
    _ = ω n * gaussEnumerated (fun q => G q x) n :=
      congrArg (fun y : ℝ => ω n * y) hF
    _ = ω n * (gaussEnumerated G n) x := by rw [← hG]

theorem flat_source_q3_finite_projected_component_gradient
    (Q : TriadicCube 2) (β : ℝ) (L : {l : ℝ // 0 < l})
    (e : Vec 2) (N : ℕ) (ω : ℕ → ℝ) (i j : Fin 2) (x : Vec 2) :
    (flatSourceQ3FiniteProjectedComponent Q β L e N ω i).grad x j =
      gaussianScalarPartialSum
        (fun n => flatSourceQ3FiniteProjectedGradientMode Q β L e i j n x) N ω := by
  rw [flatSourceQ3FiniteProjectedComponent]
  rw [h1_sum_smul_gradient]
  unfold gaussianScalarPartialSum flatSourceQ3FiniteProjectedGradientMode
  apply Finset.sum_congr rfl
  intro n hn
  let F : whiteBasisIndex → H1Function (openCubeSet Q) := fun q =>
    (lambda8Q3GaussianModeParentHessian Q β L
      (matVecMul responsePlanarJ e) q).gradCoordH1Function i
  let G : whiteBasisIndex → Vec 2 → ℝ := fun q y =>
    (lambda8Q3GaussianModeParentHessian Q β L
      (matVecMul responsePlanarJ e) q).hess i j y
  have hcoord : (fun q => (F q).grad x j) = fun q => G q x := by
    funext q
    exact Homogenization.HasWeakHessianOn.gradCoordH1Function_grad_apply _ _ _ _
  have hF := enumerated_h1_grad_apply (F := F) n x j
  rw [hcoord] at hF
  have hG := enumerated_fun_apply' G n x
  change ω n * (gaussEnumerated F n).grad x j = ω n * (gaussEnumerated G n) x
  calc
    _ = ω n * gaussEnumerated (fun q => G q x) n :=
      congrArg (fun y : ℝ => ω n * y) hF
    _ = ω n * (gaussEnumerated G n) x := by rw [← hG]

theorem flat_source_q3_finite_scalar_derivative
    (β : ℝ) (L : {l : ℝ // 0 < l}) (N : ℕ) (ω : ℕ → ℝ)
    (i : Fin 2) (x : Vec 2) :
    (fderiv ℝ (flatSourceQ3FiniteScalar β L N ω) x) (basisVec i) =
      gaussianScalarPartialSum
        (fun n => flatSourceQ3FiniteValueDerivativeMode β L i n x) N ω := by
  change (fderiv ℝ (fun y =>
    ∑ n ∈ Finset.range N, ω n *
      q3Convolution β L h3Zero (gaussEnumerated whiteBasis n) y) x)
      (basisVec i) = _
  rw [fderiv_fun_sum]
  · simp only [sum_apply]
    apply Finset.sum_congr rfl
    intro n hn
    have hconv : DifferentiableAt ℝ
        (q3Convolution β L h3Zero (gaussEnumerated whiteBasis n)) x :=
      (q3Convolution_contDiff_one β L h3Zero
        (by norm_num [h3Zero, H3Index])
        (gaussEnumerated whiteBasis n)).differentiable (by norm_num) |>.differentiableAt
    rw [fderiv_const_mul hconv]
    simp [smul_eq_mul, flatSourceQ3FiniteValueDerivativeMode]
  · intro n hn
    have hconv : DifferentiableAt ℝ
        (q3Convolution β L h3Zero (gaussEnumerated whiteBasis n)) x :=
      (q3Convolution_contDiff_one β L h3Zero
      (by norm_num [h3Zero, H3Index])
      (gaussEnumerated whiteBasis n)).differentiable (by norm_num) |>.differentiableAt
    exact hconv.const_mul (ω n)

theorem flat_source_q3_finite_product_gradient_formula
    (Q : TriadicCube 2) (β : ℝ) (L : {l : ℝ // 0 < l})
    (e : Vec 2) (N : ℕ) (ω : ℕ → ℝ) (i j : Fin 2) (x : Vec 2) :
    (flatSourceQ3FiniteProductComponent Q β L e N ω i).grad x j =
      gaussianScalarPartialSum
          (fun n => flatSourceQ3FiniteValueMode β L n x) N ω *
        gaussianScalarPartialSum
          (fun n => flatSourceQ3FiniteProjectedGradientMode Q β L e i j n x) N ω +
      gaussianScalarPartialSum
          (fun n => flatSourceQ3FiniteProjectedMode Q β L e i n x) N ω *
        gaussianScalarPartialSum
          (fun n => flatSourceQ3FiniteValueDerivativeMode β L j n x) N ω := by
  rw [flat_source_q3_finite_product_component_grad,
    flat_source_q3_finite_projected_component_gradient,
    flat_source_q3_finite_projected_component_value,
    flat_source_q3_finite_scalar_derivative]
  simp [flatSourceQ3FiniteScalar, flatSourceQ3FiniteValueMode]

end ASDExplicitGamma.Scalar
