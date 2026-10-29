module

public import ASDExplicitGamma.Inverse.LayerMeanComparison
public import ASDExplicitGamma.Inverse.LayerDensityComparison

/-! Actual deterministic layers bounded by their mean and positive errors. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
noncomputable section

/-- The literal self-label clipped layer has the source m_b v_k+a_kh cap.
Each physical cell's own old label is identified with the deterministic
layer old label before using the incoming H3 mean. -/
theorem root_self_label_clipped_layer_comparison (M : ABKModel 2) (Q : TriadicCube 2)
    (m : ℤ) (hQ : Q.scale ≤ m) (r : RootRow) (hmean : ClippedInverseMeanInput M m r)
    (hk : ℕ × ℕ) (ω : Cutoff.CutoffSample 2) (q : Vec 2) (hq : dotProduct q q=1) :
    (∑ P ∈ whitneyRootLayer Q (rootH0 r+hk.1) (hk.2+1),
      ((volume (cubeSet P)).toReal/(volume (cubeSet Q)).toReal)*
        fullMatrixQuadratic (toFullBlockVec (0,q)) (clippedCellMatrix M (P.scale+40) P (rootTau r) ω)) ≤
      rootMeanCap r*bankLayerWeight hk.2+rootMatrixPositiveError M Q r hk ω := by
  have hh := root_clipped_layer_mean_comparison M Q m hQ r hmean hk ω q hq
  apply le_trans (le_of_eq ?_) hh
  apply Finset.sum_congr rfl
  intro P hP
  have hs := root_whitney_layer_scale Q (rootH0 r+hk.1) (hk.2+1) hP
  have he : P.scale+40=rootLayerOldLabel Q (rootH0 r) hk := by
    unfold rootLayerOldLabel resetDepth
    unfold whitneyProfile at hs
    omega
  rw [he]

/-- The sum of the three actual geometric density averages has exactly
three mean terms and the three actual positive density excesses. -/
theorem root_layer_density_sum_le_excess (M : ABKModel 2) (Q : TriadicCube 2)
    (r : RootRow) (hk : ℕ × ℕ) (ω : Cutoff.CutoffSample 2) :
    (∑ e : Fin 3, ∫ x in rootLayerCarrier Q (rootH0 r+hk.1) (hk.2+1),
      (layerResolutionDiameter M Q (rootH0 r+hk.1) (rootTau r)
        (ASDExplicitGamma.Gaussian.waveGateEta (rootWaveTuple r)) (hk.2+1) e ω x)^2)/
          (volume (cubeSet Q)).toReal ≤
      3*bankLayerWeight hk.2*densityMomentBudget (rootQ r) 2 (rootMomentCutoff r)+
        ∑ e : Fin 3, resetDensityExcess M Q (rootH0 r) (rootTau r)
          (ASDExplicitGamma.Gaussian.waveGateEta (rootWaveTuple r)) (rootQ r) (rootMomentCutoff r) 2 hk e ω := by
  have hH : 333 ≤ rootH0 r := by cases r <;> norm_num [rootH0]
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun e _ =>
    layer_resolution_average_le_excess M Q (rootH0 r) hH hk (rootTau r)
      (ASDExplicitGamma.Gaussian.waveGateEta (rootWaveTuple r)) (rootQ r) (rootMomentCutoff r) e ω)
  rw [← Finset.sum_div,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
  exact hh.trans_eq (by ring)

end
end ASDExplicitGamma.Inverse
