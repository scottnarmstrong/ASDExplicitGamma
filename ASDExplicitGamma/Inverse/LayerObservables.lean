module

public import ASDExplicitGamma.Inverse.LayerPositiveComparison
public import ASDExplicitGamma.Inverse.ClippedMatrixPositiveSums

/-! The literal two deterministic-layer observables in the hybrid bound. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
noncomputable section

/-- Actual full-layer clipped pure-flux quadratic, with each cell's true
old label and physical volume weight. -/
def rootLayerClippedQuadratic (M : ABKModel 2) (Q : TriadicCube 2) (r : RootRow)
    (hk : ℕ × ℕ) (ω : Cutoff.CutoffSample 2) (q : Vec 2) : ℝ :=
  ∑ P ∈ whitneyRootLayer Q (rootH0 r+hk.1) (hk.2+1),
    ((volume (cubeSet P)).toReal/(volume (cubeSet Q)).toReal)*
      fullMatrixQuadratic (toFullBlockVec (0,q)) (clippedCellMatrix M (P.scale+40) P (rootTau r) ω)

/-- The actual sum of three physical diameter-square averages, normalized
by the root volume rather than the layer volume. -/
def rootLayerDensityAverage (M : ABKModel 2) (Q : TriadicCube 2) (r : RootRow)
    (hk : ℕ × ℕ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  (∑ e : Fin 3, ∫ x in rootLayerCarrier Q (rootH0 r+hk.1) (hk.2+1),
    (layerResolutionDiameter M Q (rootH0 r+hk.1) (rootTau r)
      (ASDExplicitGamma.Gaussian.waveGateEta (rootWaveTuple r)) (hk.2+1) e ω x)^2)/
        (volume (cubeSet Q)).toReal

theorem root_layer_clipped_quadratic_nonneg (M : ABKModel 2) (Q : TriadicCube 2)
    (r : RootRow) (hk : ℕ × ℕ) (ω : Cutoff.CutoffSample 2) (q : Vec 2) :
    0 ≤ rootLayerClippedQuadratic M Q r hk ω q := by
  apply Finset.sum_nonneg
  intro P _
  exact mul_nonneg (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
    (clipped_cell_matrix_quadratic_nonneg M _ _ _ ω _)

theorem root_layer_density_average_nonneg (M : ABKModel 2) (Q : TriadicCube 2)
    (r : RootRow) (hk : ℕ × ℕ) (ω : Cutoff.CutoffSample 2) :
    0 ≤ rootLayerDensityAverage M Q r hk ω :=
  div_nonneg (Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))) ENNReal.toReal_nonneg

end
end ASDExplicitGamma.Inverse
