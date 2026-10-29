module

public import ASDExplicitGamma.Main.CMCovariance
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Finite actual q3 gradient columns with their full Hilbert--Schmidt caps. -/

@[expose] public section
namespace ASDExplicitGamma.Main
open Homogenization ASDExplicitGamma.Gaussian
open scoped BigOperators RealInnerProductSpace

/-- A finite family of actual first spatial derivatives, in its Hilbert norm. -/
noncomputable def mainQ3FiniteColumn {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (s : Finset ι) (b : ℝ) (L : {l : ℝ // 0 < l}) (x : Vec 2) :
    EuclideanSpace ℝ (s × Fin 2) :=
  WithLp.toLp 2 (fun p => (fderiv ℝ (q3Convolution b L h3Zero (e p.1)) x) (basisVec p.2))

/-- The finite column is genuinely C1 in the spatial variable. -/
theorem mainQ3FiniteColumn_contDiff {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (s : Finset ι) (b : ℝ) (L : {l : ℝ // 0 < l}) :
    ContDiff ℝ 1 (mainQ3FiniteColumn e s b L) := by
  apply (contDiff_piLp 2).2
  intro p
  have hz : h3Zero.1.1.val+h3Zero.1.2.val ≤ 2 := by decide
  have ha : (h3Next h3Zero p.2 hz).1.1.val+
      (h3Next h3Zero p.2 hz).1.2.val ≤ 2 := by
    rcases p with ⟨j, i⟩
    fin_cases i <;> norm_num [h3Next, h3Zero]
  simpa only [mainQ3FiniteColumn, WithLp.ofLp_toLp,
    q3Convolution_fderiv_basis b L h3Zero hz] using
    q3Convolution_contDiff_one b L _ ha (e p.1)

/-- Differentiation of a Hilbert column retains the actual mixed derivatives. -/
theorem mainQ3FiniteColumn_fderiv_apply {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (s : Finset ι) (b : ℝ) (L : {l : ℝ // 0 < l}) (x : Vec 2) (k : Fin 2)
    (p : s × Fin 2) :
    ((fderiv ℝ (mainQ3FiniteColumn e s b L) x) (basisVec k)).ofLp p =
      (fderiv ℝ (fun y => (fderiv ℝ (q3Convolution b L h3Zero (e p.1)) y)
        (basisVec p.2)) x) (basisVec k) := by
  let pr : EuclideanSpace ℝ (s × Fin 2) →L[ℝ] ℝ := PiLp.proj 2 (fun _ => ℝ) p
  have h := pr.hasFDerivAt.comp x
    ((mainQ3FiniteColumn_contDiff e s b L).differentiable (by norm_num)).differentiableAt.hasFDerivAt
  exact (congrArg (fun T : Vec 2 →L[ℝ] ℝ => T (basisVec k)) h.fderiv).symm

/-- The finite column uses 31.2, the trace of the first derivative covariance,
not the smaller row operator constant 15.6. -/
theorem mainQ3FiniteColumn_norm_sq_le {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (s : Finset ι) (b : ℝ) (L : {l : ℝ // 0 < l}) (x : Vec 2) :
    ‖mainQ3FiniteColumn e s b L x‖^2 ≤ (156/5)*b^2/L.1^2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type, Finset.sum_comm]
  rw [← main_q3_first_derivative_trace e b L x]
  apply Finset.sum_le_sum
  intro i _
  have hz : h3Zero.1.1.val+h3Zero.1.2.val ≤ 2 := by decide
  have hs := (main_q3_direction_covariance e b L (h3Next h3Zero i hz)
    (h3Next h3Zero i hz) x x).summable
  have hs' : Summable (fun j => ((fderiv ℝ (q3Convolution b L h3Zero (e j)) x)
      (basisVec i))^2) := by
    simpa only [q3Convolution_fderiv_basis b L h3Zero hz, pow_two] using hs
  change (∑ j : s, ((fderiv ℝ (q3Convolution b L h3Zero (e j)) x)
    (basisVec i))^2) ≤ _
  exact (Finset.sum_coe_sort s (fun j => ((fderiv ℝ
    (q3Convolution b L h3Zero (e j)) x) (basisVec i))^2)).le.trans
      (hs'.sum_le_tsum s (fun j _ => sq_nonneg _))

/-- The full spatial Frobenius derivative cap counts both mixed Hessian entries. -/
theorem mainQ3FiniteColumn_derivative_sq_le {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (s : Finset ι) (b : ℝ) (L : {l : ℝ // 0 < l}) (x : Vec 2) :
    (∑ k : Fin 2, ‖(fderiv ℝ (mainQ3FiniteColumn e s b L) x) (basisVec k)‖^2) ≤
      (46488/25)*b^2/L.1^4 := by
  simp_rw [EuclideanSpace.real_norm_sq_eq, mainQ3FiniteColumn_fderiv_apply]
  rw [← main_q3_second_derivative_trace e b L x]
  simp_rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro k _
  have hz : h3Zero.1.1.val+h3Zero.1.2.val ≤ 2 := by decide
  have ha : (h3Next h3Zero i hz).1.1.val+(h3Next h3Zero i hz).1.2.val ≤ 2 := by
    fin_cases i <;> norm_num [h3Next, h3Zero]
  have hs := (main_q3_direction_covariance e b L
    (h3Next (h3Next h3Zero i hz) k ha)
    (h3Next (h3Next h3Zero i hz) k ha) x x).summable
  have hs' : Summable (fun j => ((fderiv ℝ (fun y =>
      (fderiv ℝ (q3Convolution b L h3Zero (e j)) y) (basisVec i)) x)
        (basisVec k))^2) := by
    simpa only [main_q3_second_coordinate, pow_two] using hs
  exact (Finset.sum_coe_sort s (fun j => ((fderiv ℝ (fun y =>
    (fderiv ℝ (q3Convolution b L h3Zero (e j)) y) (basisVec i)) x)
      (basisVec k))^2)).le.trans (hs'.sum_le_tsum s (fun j _ => sq_nonneg _))

end ASDExplicitGamma.Main
