module

public import ASDExplicitGamma.Native.OldSignedSourceDirectionalModes
public import ASDExplicitGamma.Native.OldSignedPureSecondPairing
public import ASDExplicitGamma.Native.OldSignedAffineIdentification
public import ASDExplicitGamma.Native.OldSignedFlatCellBounds
public import ASDExplicitGamma.Native.OldSignedLoadSeriesBudget
public import ASDExplicitGamma.Native.OldSignedAffineContribution
public import ASDExplicitGamma.Native.OldSignedEnergyFieldTransport

/-! The actual plus-source covariance means consume the complete source-cell
half-trace budget, with no assumed covariance or weak-energy estimate. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Algsuperdiff.Section3
noncomputable section

/-- The directional covariance energy in the literal plus-cell energy bill. -/
def oldSignedActualPlusMeanProxy (M : ABKModel 2) (n : ℤ) (r : ℕ)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) r)
    (t b : ℝ) (L : {l : ℝ // 0<l}) (ω : Cutoff.CutoffSample 2) : ℝ :=
  ∑' i,∑ c : Fin 2,oldSignedDirectionalProxy U
    (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n)
      (oldSignedCellCoefficient (originCube 2 n) U
        (openCubeSet_subset_of_mem_descendantsAtDepth hU) (oldSignedPartialResponseCoefficient n 1 t ω)))
    (oldSignedBlockMean U (oldSignedFlatInput (originCube 2 n) b L true i c)).2

/-- The actual covariance mean proxy has a finite expected value and the
sharp directional payment. Its deterministic mode summability is proved here. -/
theorem old_signed_actual_plus_mean_proxy_payment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (r : ℕ) (hr : r ≤ 5)
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1)
    (hstates : ∀ l ≤ n,nativeInductionState M h l) (b : ℝ) (L : {l : ℝ // 0<l}) :
    Integrable (oldSignedActualPlusMeanProxy M n r U hU t b L) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ ω,oldSignedActualPlusMeanProxy M n r U hU t b L ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      ((1-inverseHistoryDiscount^2)*
        ∑' j : ℕ,inverseHistoryDiscount^(2*j)*oldSignedSourceHistoryBudget M n U t j)*
          oldSignedFlatMeanSize (originCube 2 n) U b L true^2 := by
  let m := fun i c => oldSignedBlockMean U (oldSignedFlatInput (originCube 2 n) b L true i c)
  have he (i : whiteBasisIndex) (c : Fin 2) : vecNormSq (m i c).2=blockVecDot (m i c) (m i c) := by
    simp [m,oldSignedBlockMean,oldSignedFlatInput,oldSignedFlatPlusBlock,
      cubeAverage_const,blockVecDot,vecDot,vecNormSq]
  have hs : Summable (fun i => ∑ c : Fin 2,vecNormSq (m i c).2) := by
    simp_rw [he]
    exact old_signed_flat_mean_budget_series (originCube 2 n) r b L true U hU
  have hh := old_signed_source_directional_modes_payment M h hM hg n r hr U hU t ht hstates
    (fun i c => (m i c).2) hs
  have hnorm : oldSignedFlatMeanSize (originCube 2 n) U b L true^2=
      ∑' i,∑ c : Fin 2,vecNormSq (m i c).2 := by
    simp_rw [he]
    exact Real.sq_sqrt (tsum_nonneg (fun i => Finset.sum_nonneg (fun c _ =>
      add_nonneg (vecNormSq_nonneg _) (vecNormSq_nonneg _))))
  rw [hnorm]
  exact hh

end
end ASDExplicitGamma.Native
