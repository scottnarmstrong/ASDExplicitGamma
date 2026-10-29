module

public import ASDExplicitGamma.Inverse.RootMatrixDeviation
public import ASDExplicitGamma.Inverse.RootMatrixLayerWeights
public import ASDExplicitGamma.Inverse.ClippedMatrixQuadraticNorm

/-! Pathwise full-layer clipped means and the actual positive directional
error. No geometry-selected mask is inserted in the centered layer. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open scoped Matrix.Norms.Elementwise
noncomputable section

/-- Every unit pure-flux quadratic is bounded by the literal positive
directional supremum, on the whole loading population. -/
theorem clipped_unit_flux_quadratic_le_deviation (A : FullBlockMat 2) (v : Vec 2)
    (hv : dotProduct v v=1) :
    fullMatrixQuadratic (toFullBlockVec (0,v)) A ≤ clippedPositiveFluxDeviation A := by
  have hb : BddAbove {a : ℝ | ∃ u : Vec 2, dotProduct u u=1 ∧
      a=fullMatrixQuadratic (toFullBlockVec (0,u)) A} := by
    refine ⟨‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) A‖,?_⟩
    rintro y ⟨u,hu,rfl⟩
    have hh := clipped_quadratic_abs_le_norm A (toFullBlockVec (0,u))
    change |fullMatrixQuadratic (toFullBlockVec (0,u)) A| ≤ _ at hh
    have he : dotProduct (toFullBlockVec (0,u)) (toFullBlockVec (0,u))=1 := by
      simpa only [dotProduct,toFullBlockVec,Fintype.sum_sum_type,Pi.zero_apply,zero_mul,
        Finset.sum_const_zero,zero_add] using hu
    exact (le_abs_self _).trans (by simpa only [he,mul_one] using hh)
  exact (le_csSup hb ⟨v,hv,rfl⟩).trans (le_max_right _ _)

/-- Every actual deterministic layer old label is strictly protected by m. -/
theorem root_layer_old_label_lt (Q : TriadicCube 2) (m : ℤ) (hQ : Q.scale ≤ m)
    (r : RootRow) (hk : ℕ × ℕ) : rootLayerOldLabel Q (rootH0 r) hk < m := by
  have hH : 333 ≤ rootH0 r := by cases r <;> norm_num [rootH0]
  unfold rootLayerOldLabel resetDepth
  omega

/-- The source H3 mean cap and actual centered positive error bound the
full deterministic layer pathwise. Both 1.0747 inverse rows and 1.16 rows
use the same literal formula and preserve the exact layer weight. -/
theorem root_clipped_layer_mean_comparison (M : ABKModel 2) (Q : TriadicCube 2)
    (m : ℤ) (hQ : Q.scale ≤ m) (r : RootRow)
    (hmean : ClippedInverseMeanInput M m r) (hk : ℕ × ℕ) (ω : Cutoff.CutoffSample 2)
    (v : Vec 2) (hv : dotProduct v v=1) :
    (∑ U ∈ whitneyRootLayer Q (rootH0 r+hk.1) (hk.2+1),
      ((volume (cubeSet U)).toReal/(volume (cubeSet Q)).toReal)*
        fullMatrixQuadratic (toFullBlockVec (0,v))
          (clippedCellMatrix M (rootLayerOldLabel Q (rootH0 r) hk) U (rootTau r) ω)) ≤
      rootMeanCap r*bankLayerWeight hk.2+rootMatrixPositiveError M Q r hk ω := by
  classical
  let n := rootLayerOldLabel Q (rootH0 r) hk
  let s := whitneyRootLayer Q (rootH0 r+hk.1) (hk.2+1)
  let w := fun U : TriadicCube 2 => (volume (cubeSet U)).toReal/(volume (cubeSet Q)).toReal
  let L := fullMatrixQuadratic (toFullBlockVec (0,v))
  let E := fun U => ∫ ζ, clippedCellMatrix M n U (rootTau r) ζ ∂(Cutoff.cutoffSampleLaw M).toMeasure
  have hmeans : (∑ U ∈ s, w U*L (E U)) ≤ rootMeanCap r*bankLayerWeight hk.2 := by
    calc
      (∑ U ∈ s, w U*L (E U)) ≤ ∑ U ∈ s, w U*rootMeanCap r := by
        apply Finset.sum_le_sum
        intro U hU
        have hs := root_whitney_layer_scale Q (rootH0 r+hk.1) (hk.2+1) hU
        have hscale : U.scale=n-40 := by
          dsimp only [n,rootLayerOldLabel,resetDepth,whitneyProfile] at *
          omega
        have hh := hmean n (root_layer_old_label_lt Q m hQ r hk) U hscale v
        rw [hv,mul_one] at hh
        exact mul_le_mul_of_nonneg_left hh (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
      _ = _ := by rw [← Finset.sum_mul,root_matrix_layer_weights_sum]; ring
  have hcenter := clipped_unit_flux_quadratic_le_deviation (rootCenteredLayerMatrix M Q r hk ω) v hv
  change L (rootCenteredLayerMatrix M Q r hk ω) ≤ rootMatrixPositiveError M Q r hk ω at hcenter
  have he : L (rootCenteredLayerMatrix M Q r hk ω)=
      (∑ U ∈ s, w U*L (clippedCellMatrix M n U (rootTau r) ω))-(∑ U ∈ s, w U*L (E U)) := by
    simp only [rootCenteredLayerMatrix,map_sum,map_smul,map_sub,smul_eq_mul,
      mul_sub,Finset.sum_sub_distrib]
    rfl
  rw [he] at hcenter
  linarith only [hmeans,hcenter]

end
end ASDExplicitGamma.Inverse
