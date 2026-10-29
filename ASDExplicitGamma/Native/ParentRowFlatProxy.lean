module

public import ASDExplicitGamma.Native.ParentRowDirectionalModes
public import ASDExplicitGamma.Native.OldSignedPureSecondPairing
public import ASDExplicitGamma.Native.OldSignedAffineIdentification
public import ASDExplicitGamma.Native.OldSignedFlatCellBounds
public import ASDExplicitGamma.Native.OldSignedLoadSeriesBudget
public import ASDExplicitGamma.Native.OldSignedAffineContribution
public import ASDExplicitGamma.Native.OldSignedEnergyFieldTransport
public import ASDExplicitGamma.Native.OldSignedFlatDirectionalProxy

/-! Both complete flat-source affine proxy payments for the actual band.
All covariance modes are contracted before probability Cauchy--Schwarz. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Algsuperdiff.Section3
noncomputable section

/-- Both signed flat mean families consume the actual band directional
history, with genuine mode summability and no proxy bound premise. -/
theorem parent_row_flat_proxy_payment
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma≤gammaZero) (n : ℤ) (height : ℕ) (hheight : 1≤height) (hh16 : height≤16) (r : ℕ) (hr : r=5)
    (U : TriadicCube 2) (hU : U∈descendantsAtDepth (originCube 2 n) r)
    (t : ℝ) (ht : 0≤t ∧ t≤1) (hpast : ∀ k<n,nativeInductionState M h k) (hstate : nativeInductionState M h n)
    (b : ℝ) (L : {l : ℝ // 0<l}) (plus : Bool) :
    Integrable (fun omega => oldSignedFlatDirectionalMeanProxy (originCube 2 n) U
      (parentBoundaryBandFrameField M n height t omega) b L plus) (Cutoff.cutoffSampleLaw M).toMeasure ∧
    (∫ omega,oldSignedFlatDirectionalMeanProxy (originCube 2 n) U
      (parentBoundaryBandFrameField M n height t omega) b L plus ∂(Cutoff.cutoffSampleLaw M).toMeasure)≤
      ((theta M/2)*((23/100:ℝ)+t*parentBoundaryWeakMeanSlope gammaZero height+2/10^12))*
          oldSignedFlatMeanSize (originCube 2 n) U b L plus^2 := by
  let m := fun i c => oldSignedBlockMean U (oldSignedFlatInput (originCube 2 n) b L plus i c)
  let E := fun i c => if plus then (m i c).2 else (m i c).1
  have he (i : whiteBasisIndex) (c : Fin 2) : vecNormSq (E i c)=blockVecDot (m i c) (m i c) := by
    cases plus <;> simp [E,m,oldSignedBlockMean,oldSignedFlatInput,oldSignedFlatPlusBlock,
      oldSignedFlatMinusBlock,cubeAverage_const,blockVecDot,vecDot,vecNormSq]
  have hs : Summable (fun i => ∑ c : Fin 2,vecNormSq (E i c)) := by
    simp_rw [he]
    exact old_signed_flat_mean_budget_series (originCube 2 n) r b L plus U hU
  have hh := parent_row_directional_modes_payment M h hM hg n height hheight hh16 r hr U hU
    t ht hpast hstate E hs
  have hnorm : oldSignedFlatMeanSize (originCube 2 n) U b L plus^2=
      ∑' i,∑ c : Fin 2,vecNormSq (E i c) := by
    simp_rw [he]
    exact Real.sq_sqrt (tsum_nonneg (fun i => Finset.sum_nonneg (fun c _ =>
      add_nonneg (vecNormSq_nonneg _) (vecNormSq_nonneg _))))
  rw [hnorm]
  have heq (omega) : oldSignedFlatDirectionalMeanProxy (originCube 2 n) U
      (parentBoundaryBandFrameField M n height t omega) b L plus=
      ∑' i,∑ c : Fin 2,oldSignedDirectionalProxy U
        (responseFramePlanarCoefficientField M.nu (Annealed.sigmaBar M n)
          (oldSignedCellCoefficient (originCube 2 n) U (openCubeSet_subset_of_mem_descendantsAtDepth hU)
            (pureFluxOpenResponseRestriction n (nativeSourceBandScalar n height t omega)))) (E i c) := by
    dsimp only [parentBoundaryBandFrameField]
    rw [←old_signed_flat_directional_proxy_cell_eq (originCube 2 n) U
      (openCubeSet_subset_of_mem_descendantsAtDepth hU) M.nu (Annealed.sigmaBar M n)
      M.nu_pos (Annealed.sigmaBar_characterization M n).1
      (pureFluxOpenResponseRestriction n (nativeSourceBandScalar n height t omega)) b L plus]
    rfl
  simp_rw [heq]
  exact hh

end
end ASDExplicitGamma.Native
