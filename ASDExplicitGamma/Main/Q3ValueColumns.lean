module

public import ASDExplicitGamma.Main.Q3RowCovariance
public import ASDExplicitGamma.Main.EuclideanMeanValue
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Actual q3 value columns with sharp spatial Euclidean Lipschitz control. -/

@[expose] public section
namespace ASDExplicitGamma.Main
open Homogenization ASDExplicitGamma.Gaussian ASDExplicitGamma.Model ASDExplicitGamma.Triadic
open scoped BigOperators

noncomputable def mainQ3FiniteValue {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (s : Finset ι) (b : ℝ) (L : {l : ℝ // 0 < l}) (x : Vec 2) : EuclideanSpace ℝ s :=
  WithLp.toLp 2 (fun j => q3Convolution b L h3Zero (e j) x)

theorem mainQ3FiniteValue_contDiff {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (s : Finset ι) (b : ℝ) (L : {l : ℝ // 0 < l}) :
    ContDiff ℝ 1 (mainQ3FiniteValue e s b L) :=
  (contDiff_piLp 2).2 fun j => (main_q3_value_direction_contDiff_three b L (e j)).of_le (by norm_num)

/-- Continuous linear maps retain the actual two spatial components. -/
theorem main_planar_clm_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : Vec 2 →L[ℝ] F) (v : Vec 2) : T v = ∑ i, v i • T (basisVec i) := by
  have hv : v = ∑ i, v i • basisVec i := by
    ext i
    fin_cases i <;> simp [Fin.sum_univ_two, basisVec]
  conv_lhs => rw [hv]
  rw [map_sum]
  simp only [map_smul]

/-- The actual derivative of each value column is its physical first jet. -/
theorem mainQ3FiniteValue_fderiv {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (s : Finset ι) (b : ℝ) (L : {l : ℝ // 0 < l}) (x v : Vec 2) (j : s) :
    ((fderiv ℝ (mainQ3FiniteValue e s b L) x) v).ofLp j =
      ∑ i, v i*q3Convolution b L (mainQ3JetIndex (.first i)) (e j) x := by
  let pr : EuclideanSpace ℝ s →L[ℝ] ℝ := PiLp.proj 2 (fun _ => ℝ) j
  have h := pr.hasFDerivAt.comp x
    ((mainQ3FiniteValue_contDiff e s b L).differentiable (by norm_num)).differentiableAt.hasFDerivAt
  have he := (congrArg (fun T : Vec 2 →L[ℝ] ℝ => T v) h.fderiv).symm
  change ((fderiv ℝ (mainQ3FiniteValue e s b L) x) v).ofLp j =
    (fderiv ℝ (q3Convolution b L h3Zero (e j)) x) v at he
  rw [he, main_planar_clm_apply]
  congr 1
  funext i
  rw [smul_eq_mul, q3Convolution_fderiv_basis b L h3Zero (by decide)]
  congr 2
  fin_cases i <;> rfl

/-- The spatial derivative OPERATOR cap uses isotropy, not its doubled trace. -/
theorem mainQ3FiniteValue_derivative_bound {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (s : Finset ι) (b : ℝ) (L : {l : ℝ // 0 < l}) (x v : Vec 2) :
    ‖(fderiv ℝ (mainQ3FiniteValue e s b L) x) v‖^2 ≤
      ((78/5)*b^2/L.1^2)*mainSpatialDistanceSq v 0 := by
  let X := fun j i => q3Convolution b L (mainQ3JetIndex (.first i)) (e j) x
  have hh (i k : Fin 2) := main_q3_jet_covariance e b L (.first i) (.first k) x
  have hs := summable_sq_finset_sum Finset.univ v X (fun i _ k _ => (hh i k).summable)
  have ht := tsum_sq_finset_sum Finset.univ v X (fun i _ k _ => (hh i k).summable)
  dsimp only [X] at ht
  simp_rw [(fun i k => (hh i k).tsum_eq)] at ht
  rw [q3ScaledJetCovariance_first_quadratic] at ht
  rw [EuclideanSpace.real_norm_sq_eq]
  simp_rw [mainQ3FiniteValue_fderiv]
  have hb := hs.sum_le_tsum s (fun j _ => sq_nonneg _)
  rw [ht] at hb
  change (∑ j : s, (∑ i, v i*X j i)^2) ≤ _
  rw [Finset.sum_coe_sort s (fun j => (∑ i, v i*X j i)^2)]
  simpa only [mainSpatialDistanceSq, Pi.zero_apply, sub_zero, mul_div_assoc] using hb

/-- Sharp global Euclidean Lipschitz control of the actual finite value factor. -/
theorem main_q3_value_difference_sq {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (s : Finset ι) (b : ℝ) (L : {l : ℝ // 0 < l}) (x y : Vec 2) :
    ‖mainQ3FiniteValue e s b L x-mainQ3FiniteValue e s b L y‖^2 ≤
      ((78/5)*b^2/L.1^2)*mainSpatialDistanceSq x y := by
  have h := main_euclidean_mean_value
    ((mainQ3FiniteValue_contDiff e s b L).differentiable (by norm_num))
    (Real.sqrt_nonneg ((78/5)*b^2/L.1^2))
    (fun z v => by
      rw [Real.sq_sqrt (by positivity : 0 ≤ (78/5:ℝ)*b^2/L.1^2)]
      exact mainQ3FiniteValue_derivative_bound e s b L z v) x y
  rwa [Real.sq_sqrt (by positivity : 0 ≤ (78/5:ℝ)*b^2/L.1^2)] at h

end ASDExplicitGamma.Main
