module

public import ASDExplicitGamma.Native.OldSignedDirectionalProxyCongr
public import ASDExplicitGamma.Native.OldSignedFlatDirectionalProxySeries
public import ASDExplicitGamma.Native.OldSignedMinusDirectionalProxySeries

/-! A common display-field name for both actual affine covariance proxies. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian
noncomputable section

/-- Complete directional covariance proxy of the genuine flat cell means.
The Boolean selects the existing plus or minus physical source. -/
def oldSignedFlatDirectionalMeanProxy (Q U : TriadicCube 2) (a : CoeffField 2)
    (b : ℝ) (L : {l : ℝ // 0<l}) (plus : Bool) : ℝ :=
  ∑' n : whiteBasisIndex,∑ i : Fin 2,oldSignedDirectionalProxy U a
    (if plus then (oldSignedBlockMean U (oldSignedFlatInput Q b L plus n i)).2
      else (oldSignedBlockMean U (oldSignedFlatInput Q b L plus n i)).1)

/-- Restriction to the literal cell coefficient preserves the entire
covariance proxy, including every inverse depth. -/
theorem old_signed_flat_directional_proxy_cell_eq (Q U : TriadicCube 2)
    (hsub : openCubeSet U ⊆ openCubeSet Q)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l}) (plus : Bool) :
    oldSignedFlatDirectionalMeanProxy Q U
      (responseFramePlanarCoefficientField nu sigma (oldSignedCellCoefficient Q U hsub k)) b L plus=
    oldSignedFlatDirectionalMeanProxy Q U (responseFramePlanarCoefficientField nu sigma k) b L plus := by
  apply tsum_congr
  intro n
  apply Finset.sum_congr rfl
  intro i _
  apply old_signed_directional_proxy_congr U _ _
    (responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet U)
      nu sigma hnu hsigma _)
    ((responseFramePlanarCoefficientField_isElliptic (measurableSet_openCubeSet Q)
      nu sigma hnu hsigma k).mono (measurableSet_openCubeSet U) hsub)
  exact old_signed_cell_frame_coefficient_ae Q U hsub nu sigma k

/-- The common display-field proxy is nonnegative on every actual cell. -/
theorem old_signed_flat_directional_proxy_nonneg (Q U : TriadicCube 2)
    (hsub : openCubeSet U ⊆ openCubeSet Q)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0<l}) (plus : Bool) :
    0≤oldSignedFlatDirectionalMeanProxy Q U (responseFramePlanarCoefficientField nu sigma k) b L plus := by
  rw [←old_signed_flat_directional_proxy_cell_eq Q U hsub nu sigma hnu hsigma k b L plus]
  apply tsum_nonneg
  intro n
  apply Finset.sum_nonneg
  intro i _
  exact (old_signed_directional_proxy_nonneg_le U nu sigma hnu hsigma _ _).1

end
end ASDExplicitGamma.Native
