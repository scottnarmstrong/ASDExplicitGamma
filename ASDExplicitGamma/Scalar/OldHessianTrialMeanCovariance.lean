module

public import ASDExplicitGamma.Scalar.OldHessianTrialFrozenAlgebra
public import ASDExplicitGamma.Inverse.PureFluxGeneratorRowSource
public import ASDExplicitGamma.Native.OldSignedFlatMeans
public import ASDExplicitGamma.Native.OldSignedSeriesPairingBudget

/-! The literal complete frozen covariance on each fine source cell.
Its modes are the original finite-parent minus fields and physical white
coefficient means; convergence precedes every signed rearrangement. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main
noncomputable section

/-- Frozen mean covariance of the original finite-parent minus family. -/
def oldHessianMeanCovariance (Q U : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0<l}) : Mat 2 :=
  fun k i => ∑' j : whiteBasisIndex,
    cubeAverage U (q3Convolution b L h3Zero (whiteBasis j))*
      (oldSignedBlockMean U (oldSignedFlatMinusBlock Q b L j i)).1 k

/-- All coefficient cell means have a genuinely summable square series
bounded by the one physical variance. -/
theorem old_hessian_coefficient_mean_squares (U : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) :
    Summable (fun j : whiteBasisIndex =>
      cubeAverage U (q3Convolution b L h3Zero (whiteBasis j))^2) ∧
      (∑' j : whiteBasisIndex,cubeAverage U (q3Convolution b L h3Zero (whiteBasis j))^2) ≤ b^2 := by
  have hn (j : whiteBasisIndex) := sq_nonneg
    (cubeAverage U (q3Convolution b L h3Zero (whiteBasis j)))
  have hb := fun s => pureFluxMainQ3_cellMeanSquare_bound whiteBasis s b L U
  exact ⟨summable_of_sum_le hn hb,Real.tsum_le_of_sum_le hn hb⟩

/-- Each actual minus-field cell-mean coordinate is square summable. -/
theorem old_hessian_minus_mean_coordinate_squares (Q : TriadicCube 2) (depth : ℕ)
    (b : ℝ) (L : {l : ℝ // 0<l}) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth Q depth) (i k : Fin 2) :
    Summable (fun j : whiteBasisIndex =>
      ((oldSignedBlockMean U (oldSignedFlatMinusBlock Q b L j i)).1 k)^2) := by
  apply (old_signed_flat_minus_mean_series Q depth b L i U hU).of_nonneg_of_le
    (fun j => sq_nonneg _)
  intro j
  let p := oldSignedBlockMean U (oldSignedFlatMinusBlock Q b L j i)
  have hs : (p.1 k)^2≤∑ l : Fin 2,(p.1 l)^2 :=
    Finset.single_le_sum (fun l _ => sq_nonneg (p.1 l)) (Finset.mem_univ k)
  have hs' : (p.1 k)^2≤vecNormSq p.1 := by
    simpa only [vecNormSq,vecDot,pow_two] using hs
  exact hs'.trans (le_add_of_nonneg_right (vecNormSq_nonneg p.2))

/-- Every frozen matrix entry is a convergent actual complete-mode series,
with constant-one covariance Cauchy bound. -/
theorem old_hessian_mean_covariance_entry (Q : TriadicCube 2) (depth : ℕ)
    (b : ℝ) (L : {l : ℝ // 0<l}) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth Q depth) (i k : Fin 2) :
    Summable (fun j : whiteBasisIndex =>
      cubeAverage U (q3Convolution b L h3Zero (whiteBasis j))*
        (oldSignedBlockMean U (oldSignedFlatMinusBlock Q b L j i)).1 k) ∧
      |oldHessianMeanCovariance Q U b L k i| ≤ |b| * Real.sqrt
        (∑' j : whiteBasisIndex,((oldSignedBlockMean U (oldSignedFlatMinusBlock Q b L j i)).1 k)^2) := by
  let a := fun j : whiteBasisIndex => cubeAverage U (q3Convolution b L h3Zero (whiteBasis j))
  let m := fun j : whiteBasisIndex => (oldSignedBlockMean U (oldSignedFlatMinusBlock Q b L j i)).1 k
  have ha := old_hessian_coefficient_mean_squares U b L
  have hm := old_hessian_minus_mean_coordinate_squares Q depth b L U hU i k
  have hc := old_signed_series_pairing_budget (fun j => |a j|) (fun j => |m j|) (fun j => a j*m j)
    (fun j => abs_nonneg _) (fun j => abs_nonneg _)
    (by simpa only [sq_abs] using ha.1) (by simpa only [sq_abs] using hm)
    (fun j => (abs_mul (a j) (m j)).le)
  simp only [sq_abs] at hc
  have hr : Real.sqrt (∑' j,a j^2)≤|b| := by
    simpa only [Real.sqrt_sq_eq_abs] using Real.sqrt_le_sqrt ha.2
  exact ⟨hc.1,hc.2.trans (mul_le_mul_of_nonneg_right hr (Real.sqrt_nonneg _))⟩

/-- The actual deterministic frozen covariance remainder, retaining both
the finite-parent boundary and cell oscillation contributions. -/
def oldHessianMeanCovarianceError (Q U : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0<l}) : Mat 2 :=
  oldHessianMeanCovariance Q U b L-(b^2/2) • responsePlanarJ

theorem old_hessian_mean_covariance_split (Q U : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0<l}) :
    oldHessianMeanCovariance Q U b L=
      (b^2/2) • responsePlanarJ+oldHessianMeanCovarianceError Q U b L := by
  unfold oldHessianMeanCovarianceError
  abel

end
end ASDExplicitGamma.Scalar
