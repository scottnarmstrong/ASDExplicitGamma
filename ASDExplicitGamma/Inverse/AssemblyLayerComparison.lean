module

public import ASDExplicitGamma.Inverse.AssemblyLayerSums
public import ASDExplicitGamma.Inverse.AssemblyDensity
public import ASDExplicitGamma.Inverse.LayerMeanComparison
public import ASDExplicitGamma.Inverse.LayerDensityComparison

/-! Mean plus actual positive error on each deterministic layer. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
open scoped Matrix.Norms.Elementwise
noncomputable section

/-- The actual layer's clipped pure-flux quadratic. -/
def assemblyClippedQuadratic (M : ABKModel 2) (Q : TriadicCube 2)
    (H i : ℕ) (ω : Cutoff.CutoffSample 2) (q : Vec 2) : ℝ :=
  ∑ P ∈ whitneyRootLayer Q H i,
    ((volume (cubeSet P)).toReal/(volume (cubeSet Q)).toReal) *
      fullMatrixQuadratic (toFullBlockVec (0,q))
        (clippedCellMatrix M (P.scale+40) P resetAllOrderTau ω)

/-- The three actual geometric resolution-square averages on a layer. -/
def assemblyGeometricDensityAverage (M : ABKModel 2) (Q : TriadicCube 2)
    (H i : ℕ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  (∑ e : Fin 3, ∫ x in rootLayerCarrier Q H i,
    (layerResolutionDiameter M Q H resetAllOrderTau (waveGateEta .allOrder)
      i e ω x)^2)/(volume (cubeSet Q)).toReal

/-- Protected native means and the actual positive directional deviation
control every deterministic clipped layer. -/
theorem assembly_clipped_layer_mean_comparison (M : ABKModel 2) (h : ℝ)
    (hγ : M.gamma ≤ gammaZero) (Q : TriadicCube 2) (k H : ℕ)
    (hH : heightEntrance k ≤ H)
    (hpast : ∀ n : ℤ, n ≤ Q.scale-342-12*k → nativeInductionState M h n)
    (i : ℕ) (ω : Cutoff.CutoffSample 2) (v : Vec 2) (hv : dotProduct v v=1) :
    assemblyClippedQuadratic M Q H (i+1) ω v ≤
      (29/25:ℝ)*bankLayerWeight i +
        resetRootMatrixPositiveError M Q H (i+1) resetAllOrderTau ω := by
  classical
  let n := layerOldCutoff Q.scale H (i+1)
  let s := whitneyRootLayer Q H (i+1)
  let w := fun U : TriadicCube 2 =>
    (volume (cubeSet U)).toReal/(volume (cubeSet Q)).toReal
  let L := fullMatrixQuadratic (toFullBlockVec (0,v))
  let E := fun U => ∫ ζ, clippedCellMatrix M n U resetAllOrderTau ζ
    ∂(Cutoff.cutoffSampleLaw M).toMeasure
  have hcut := layer_old_cutoff_le_protected Q.scale k H (i+1) hH (by omega)
  have hstate : nativeInductionState M h n := hpast n (by
    simpa only [protectedOldLabel] using hcut)
  obtain ⟨hhist,hmean,hnu,hscalar⟩ := reset_native_coordinates M h n hstate
  have hunit : dotProduct (toFullBlockVec (0,v)) (toFullBlockVec (0,v))=1 := by
    simpa only [dotProduct,toFullBlockVec,Fintype.sum_sum_type,Pi.zero_apply,
      zero_mul,Finset.sum_const_zero,zero_add] using hv
  have hmeans : (∑ U ∈ s, w U*L (E U)) ≤ (29/25:ℝ)*bankLayerWeight i := by
    calc
      _ ≤ ∑ U ∈ s, w U*(29/25:ℝ) := by
        apply Finset.sum_le_sum
        intro U hU
        have hlabel := root_whitney_old_cutoff_eq Q H (i+1) hU
        have hscale : U.scale=n-40 := by dsimp only [n]; omega
        have hh := clipped_cell_matrix_mean_le M n U hscale
          M.shellPrefix.gamma_pos hγ hmean resetAllOrderTau (toFullBlockVec (0,v))
        rw [hunit,mul_one] at hh
        exact mul_le_mul_of_nonneg_left hh
          (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
      _ = _ := by
        rw [← Finset.sum_mul,root_matrix_layer_weights_sum]
        ring
  have hcenter := clipped_unit_flux_quadratic_le_deviation
    (resetRootCenteredLayerMatrix M Q H (i+1) resetAllOrderTau ω) v hv
  change L (resetRootCenteredLayerMatrix M Q H (i+1) resetAllOrderTau ω) ≤
    resetRootMatrixPositiveError M Q H (i+1) resetAllOrderTau ω at hcenter
  have he : L (resetRootCenteredLayerMatrix M Q H (i+1) resetAllOrderTau ω) =
      (∑ U ∈ s, w U*L (clippedCellMatrix M n U resetAllOrderTau ω)) -
        (∑ U ∈ s, w U*L (E U)) := by
    simp only [resetRootCenteredLayerMatrix,map_sum,map_smul,map_sub,smul_eq_mul,
      mul_sub,Finset.sum_sub_distrib]
    rfl
  rw [he] at hcenter
  have hself : assemblyClippedQuadratic M Q H (i+1) ω v =
      ∑ U ∈ s, w U*L (clippedCellMatrix M n U resetAllOrderTau ω) := by
    apply Finset.sum_congr rfl
    intro U hU
    have hlabel := root_whitney_old_cutoff_eq Q H (i+1) hU
    change _ = w U * L (clippedCellMatrix M n U resetAllOrderTau ω)
    rw [show U.scale+40=n from hlabel.symm]
  rw [hself]
  linarith only [hmeans,hcenter]

/-- Every geometric density average is its rare mean plus its own positive
excess, with all three resolution labels retained literally. -/
theorem assembly_geometric_density_sum_le_excess (M : ABKModel 2)
    (Q : TriadicCube 2) (H0 : ℕ) (hH0 : 333 ≤ H0)
    (hk : ℕ × ℕ) (ω : Cutoff.CutoffSample 2) :
    assemblyGeometricDensityAverage M Q (H0+hk.1) (hk.2+1) ω ≤
      3*bankLayerWeight hk.2*densityMomentBudget (allOrderDensity:ℝ) 2 1324 +
        ∑ e : Fin 3, resetDensityExcess M Q H0 resetAllOrderTau
          (waveGateEta .allOrder) (allOrderDensity:ℝ) 1324 2 hk e ω := by
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun e _ =>
    layer_resolution_average_le_excess M Q H0 hH0 hk resetAllOrderTau
      (waveGateEta .allOrder) (allOrderDensity:ℝ) 1324 e ω)
  rw [← Finset.sum_div,Finset.sum_add_distrib,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
  exact hh.trans_eq (by ring)

end
end ASDExplicitGamma.Inverse
