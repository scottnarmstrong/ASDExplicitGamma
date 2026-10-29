module

public import ASDExplicitGamma.Inverse.RootDefinitions

/-! The first-local and full rows' source H3 premise follows directly from
the strictly earlier frozen native buffer means. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization Algsuperdiff.Section3
open scoped Matrix.Norms.Elementwise
noncomputable section

/-- Native earlier buffer means supply the exact 29/25 inverse-compressed
clipped mean, for either row using the full-matrix cap. The two 1.0747 rows
retain their separate source H3 input. -/
theorem clipped_inverse_mean_input_first_full (M : ABKModel 2) (h : ℝ)
    (hg : M.gamma ≤ gammaZero) (m : ℤ) (r : RootRow)
    (hr : r=.firstLocal ∨ r=.full) (hpast : ∀ n < m, nativeInductionState M h n) :
    ClippedInverseMeanInput M m r := by
  have hcap (τ : ℝ) (n : ℤ) (hn : n < m) (U : TriadicCube 2) (hU : U.scale=n-40) (v : Vec 2) :
      fullMatrixQuadratic (toFullBlockVec (0,v))
        (∫ ω, clippedCellMatrix M n U τ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
          (29/25:ℝ)*dotProduct v v := by
    have hb := (reset_native_coordinates M h n (hpast n hn)).2.1
    have hh := clipped_cell_matrix_mean_le M n U hU M.shellPrefix.gamma_pos hg hb τ (toFullBlockVec (0,v))
    have he : dotProduct (toFullBlockVec (0,v)) (toFullBlockVec (0,v)) = dotProduct v v := by
      simp only [dotProduct,toFullBlockVec,Fintype.sum_sum_type,Pi.zero_apply,zero_mul,
        Finset.sum_const_zero,zero_add]
    rwa [he] at hh
  rcases hr with rfl | rfl
  · exact hcap (rootTau .firstLocal)
  · exact hcap (rootTau .full)

end
end ASDExplicitGamma.Inverse
