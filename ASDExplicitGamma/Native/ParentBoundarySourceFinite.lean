module

public import ASDExplicitGamma.Native.ParentBoundaryProduct
public import ASDExplicitGamma.Main.Q3ColumnH1Product
public import ASDExplicitGamma.Main.HilbertFiniteCoordinates

/-! Exact finite-coordinate trace of the physical parent source column.
The independent comparison cells all restrict the same parent potential. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Triadic ASDExplicitGamma.Main
noncomputable section

/-- Literal mode energy of the parent potential times the physical first
q3 derivative column, before its norm-preserving planar rotation. -/
def parentBoundaryPotentialSourceMode {ι : Type*} (e : HilbertBasis ι ℝ WhiteNoise)
    (Q : TriadicCube 2) (depth : ℕ) (u : H10Function (openCubeSet Q))
    (b : ℝ) (L : {l : ℝ // 0<l}) (n : ι) : ℝ :=
  descendantsAverage Q depth (fun U => vectorPositiveHaarNorm U
    (fun x i => u.toH1Function x*(fderiv ℝ (q3Convolution b L h3Zero (e n)) x) (basisVec i))^2)

/-- Finite source coordinates give exactly the genuine Hilbert positive
energy, including their zero modes and every positive Haar increment. -/
theorem parent_boundary_source_finite_cell {ι : Type*}
    (e : HilbertBasis ι ℝ WhiteNoise) (s : Finset ι) (Q U : TriadicCube 2)
    (depth : ℕ) (hU : U ∈ descendantsAtDepth Q depth)
    (u : H10Function (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l}) :
    (∑ n ∈ s,vectorPositiveHaarNorm U
      (fun x i => u.toH1Function x*(fderiv ℝ (q3Convolution b L h3Zero (e n)) x) (basisVec i))^2) =
    hilbertPositiveHaarNorm U (Real.sqrt 3)
      (fun x => u.toH1Function x • mainQ3FiniteColumn e s b L x)^2 := by
  let v := u.toH1Function.restrictToOpenSubcube hU
  have hm : MemLp (fun x => u.toH1Function x • mainQ3FiniteColumn e s b L x)
      2 (normalizedCubeMeasure U) :=
    (mainRankOneMultiplier U (mainQ3FiniteColumn e s b L)
      (mainQ3FiniteColumn_contDiff e s b L)).product_memLp v.memL2_normalizedCubeMeasure
  have hs := (main_q3_column_h1_product e s b L U v).1
  have hp := main_hilbertPrimalEnergy_euclidean U hm hs
  have hn : 0≤hilbertPrimalEnergy U (Real.sqrt 3)
      (fun x => u.toH1Function x • mainQ3FiniteColumn e s b L x) := by
    unfold hilbertPrimalEnergy
    exact add_nonneg (hilbertEnergy_nonneg U _) (tsum_nonneg (fun _ => mul_nonneg (by positivity) (hilbertEnergy_nonneg U _)))
  rw [hilbertPositiveHaarNorm,Real.sq_sqrt hn]
  rw [hp,Fintype.sum_prod_type]
  rw [←Finset.sum_coe_sort s]
  apply Finset.sum_congr rfl
  intro n _
  rw [vectorPositiveHaarNorm_sq]
  apply Finset.sum_congr rfl
  intro i _
  have he : (fun x => (u.toH1Function x • mainQ3FiniteColumn e s b L x).ofLp (n,i)) =
      (fun x => u.toH1Function x*(fderiv ℝ (q3Convolution b L h3Zero (e n)) x) (basisVec i)) := by
    funext x
    simp only [PiLp.smul_apply,mainQ3FiniteColumn,smul_eq_mul]
  rw [he,positiveHaarNorm,Real.sq_sqrt (primalEnergy_nonneg U (Real.sqrt 3) (Real.sqrt_nonneg _) _)]

end
end ASDExplicitGamma.Native
