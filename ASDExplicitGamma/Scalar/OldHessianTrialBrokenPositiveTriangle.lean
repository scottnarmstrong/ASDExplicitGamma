module

public import ASDExplicitGamma.Scalar.OldHessianTrialSeriesTriangle
public import ASDExplicitGamma.Native.OldSignedDescendantMinkowski
public import ASDExplicitGamma.Triadic.VectorPositiveMultiplier
public import ASDExplicitGamma.Variational.LemmaVTiles

/-! Complete broken positive-energy Minkowski for actual covariance source
columns, including their cell-dependent frozen means. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Triadic Variational
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- Literal fine-cell average of a cell-dependent vector column energy. -/
def oldHessianBrokenColumnEnergy (Q : TriadicCube 2) (fine : ℕ)
    (F : TriadicCube 2 → Vec 2 → Vec 2) : ℝ :=
  descendantsAverage Q fine (fun U => vectorPositiveHaarEnergy U (F U))

theorem old_hessian_broken_column_energy_nonneg (Q : TriadicCube 2) (fine : ℕ)
    (F : TriadicCube 2 → Vec 2 → Vec 2) : 0≤oldHessianBrokenColumnEnergy Q fine F :=
  descendantsAverage_nonneg Q fine _ (fun U _ => vectorPositiveHaarEnergy_nonneg U _)

/-- Complete white-mode and fine-cell aggregation retains constant one and
supplies convergence of the mixed energy, even with cell-dependent columns. -/
theorem old_hessian_broken_cell_positive_triangle {I : Type*} (Q : TriadicCube 2) (fine : ℕ)
    (F G : I → TriadicCube 2 → Vec 2 → Vec 2)
    (hFm : ∀ j U, U ∈ descendantsAtDepth Q fine → ∀ k,
      MemLp (fun x => F j U x k) 2 (normalizedCubeMeasure U))
    (hGm : ∀ j U, U ∈ descendantsAtDepth Q fine → ∀ k,
      MemLp (fun x => G j U x k) 2 (normalizedCubeMeasure U))
    (hFp : ∀ j U, U ∈ descendantsAtDepth Q fine → ∀ k,
      Summable (fun d => (Real.sqrt 3)^(d+1)*energy U (cubeIncrement U (d+1) (fun x => F j U x k))))
    (hGp : ∀ j U, U ∈ descendantsAtDepth Q fine → ∀ k,
      Summable (fun d => (Real.sqrt 3)^(d+1)*energy U (cubeIncrement U (d+1) (fun x => G j U x k))))
    (hFs : Summable (fun j => oldHessianBrokenColumnEnergy Q fine (F j)))
    (hGs : Summable (fun j => oldHessianBrokenColumnEnergy Q fine (G j))) :
    Summable (fun j => oldHessianBrokenColumnEnergy Q fine (fun U x k => F j U x k+G j U x k)) ∧
      Real.sqrt (∑' j,oldHessianBrokenColumnEnergy Q fine (fun U x k => F j U x k+G j U x k)) ≤
        Real.sqrt (∑' j,oldHessianBrokenColumnEnergy Q fine (F j))+
          Real.sqrt (∑' j,oldHessianBrokenColumnEnergy Q fine (G j)) := by
  have hf0 j := old_hessian_broken_column_energy_nonneg Q fine (F j)
  have hg0 j := old_hessian_broken_column_energy_nonneg Q fine (G j)
  have hc0 j := old_hessian_broken_column_energy_nonneg Q fine (fun U x k => F j U x k+G j U x k)
  have hroot (j : I) : Real.sqrt (oldHessianBrokenColumnEnergy Q fine (fun U x k => F j U x k+G j U x k)) ≤
      Real.sqrt (oldHessianBrokenColumnEnergy Q fine (F j))+
        Real.sqrt (oldHessianBrokenColumnEnergy Q fine (G j)) := by
    have hd := old_signed_descendant_sqrt_energy_bound Q fine
      (fun U => vectorPositiveHaarEnergy U (F j U)) (fun U => vectorPositiveHaarEnergy U (G j U))
      (fun U => vectorPositiveHaarNorm U (fun x k => F j U x k+G j U x k))
      (by norm_num : (0:ℝ)≤1) (by norm_num : (0:ℝ)≤1)
      (fun U _ => vectorPositiveHaarEnergy_nonneg U _) (fun U _ => vectorPositiveHaarEnergy_nonneg U _)
      (fun U _ => Real.sqrt_nonneg _) (fun U hU => by
        simpa only [one_mul,vectorPositiveHaarNorm] using
          (vectorPositiveHaar_add_le U (F j U) (G j U) (hFm j U hU) (hGm j U hU) (hFp j U hU) (hGp j U hU)).2)
    simpa only [oldHessianBrokenColumnEnergy,one_mul,vectorPositiveHaarNorm,
      Real.sq_sqrt (vectorPositiveHaarEnergy_nonneg _ _)] using hd
  have hh := old_hessian_series_energy_triangle
    (fun j => Real.sqrt (oldHessianBrokenColumnEnergy Q fine (F j)))
    (fun j => Real.sqrt (oldHessianBrokenColumnEnergy Q fine (G j)))
    (fun j => Real.sqrt (oldHessianBrokenColumnEnergy Q fine (fun U x k => F j U x k+G j U x k)))
    (fun j => Real.sqrt_nonneg _) (fun j => Real.sqrt_nonneg _) (fun j => Real.sqrt_nonneg _)
    (by simpa only [Real.sq_sqrt (hf0 _)] using hFs)
    (by simpa only [Real.sq_sqrt (hg0 _)] using hGs) hroot
  simpa only [Real.sq_sqrt (hf0 _),Real.sq_sqrt (hg0 _),Real.sq_sqrt (hc0 _)] using hh

end
end ASDExplicitGamma.Scalar
