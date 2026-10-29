module

public import ASDExplicitGamma.Native.ParentBoundaryWeakSourceReturn
public import ASDExplicitGamma.Native.ParentWeakRareSeries

/-! The exact complete leading mean, with no loss of the half-trace factor. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Main Triadic Cold Algsuperdiff.Section3
noncomputable section

/-- The full bank-weighted mean series is summable and retains the literal
.23 theta initial coordinate and the exact primitive weak slope. -/
theorem parent_weak_leading_mean_return
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (hg : M.gamma ≤ gammaZero)
    (n : ℤ) (height : ℕ) (hheight : 1 ≤ height)
    (hpast : ∀ k<n,nativeInductionState M h k) (hstate : nativeInductionState M h n)
    (depth : ℕ) (hdepth : depth=5) (U : TriadicCube 2)
    (hU : U∈descendantsAtDepth (originCube 2 n) depth) (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) :
    let f := fun j : ℕ => (3683/2500:ℝ)*inverseHistoryDiscount^(2*j)*bankDepthFrame M j*
      (∫ ω,parentBoundaryBandCellTrace M n height t U j ω ∂(Cutoff.cutoffSampleLaw M).toMeasure)
    Summable f ∧ (1-inverseHistoryDiscount^2)*(∑' j : ℕ,f j) ≤
      theta M*((23/100:ℝ)+t*parentBoundaryWeakMeanSlope gammaZero height) := by
  intro f
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let b : ℝ := 3683/2500
  let a := fun j : ℕ => b*inverseHistoryDiscount^(2*j)*bankDepthFrame M j*
    (∫ ω,cutoffTraceDefect M n (n-((5+j:ℕ):ℤ)) ω ∂μ)
  let d := fun j : ℕ => b*inverseHistoryDiscount^(2*j)*bankDepthFrame M j*
    parentBoundaryMeanDepthSlope M.gamma height j
  have hi := old_signed_initial_weighted_mean M h hM hg n hpast hstate
  dsimp only at hi
  have has : Summable a := (hi.1.mul_left b).congr (fun j => by dsimp only [a]; ring)
  have hd := parent_boundary_weak_mean_slope_sum M hg height
  have hds : Summable d := hd.1
  have hpoint (j : ℕ) : f j ≤ a j+t*d j := by
    have hm := parent_boundary_weak_cell_mean_return M h hM hg n height hheight hpast hstate depth hdepth U hU t ht.1 ht.2 j
    have hw : 0 ≤ b*inverseHistoryDiscount^(2*j)*bankDepthFrame M j :=
      mul_nonneg (mul_nonneg (by norm_num [b]) (pow_nonneg inverse_history_discount_range.1.le _))
        (bankDepthFrame_pos M j).le
    exact (mul_le_mul_of_nonneg_left hm hw).trans_eq (by dsimp only [f,a,d,b,μ]; ring)
  have hf0 (j : ℕ) : 0 ≤ f j := by
    apply mul_nonneg
    · exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg inverse_history_discount_range.1.le _))
        (bankDepthFrame_pos M j).le
    · apply integral_nonneg
      intro ω
      unfold parentBoundaryBandCellTrace descendantsAverage
      exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Finset.sum_nonneg
        (fun V _ => parent_boundary_band_trace_nonneg M n height t V ω))
  have hfs : Summable f := Summable.of_nonneg_of_le hf0 hpoint (has.add (hds.mul_left t))
  have hsum := hfs.tsum_le_tsum hpoint (has.add (hds.mul_left t))
  have hdis : 0 ≤ 1-inverseHistoryDiscount^2 := sub_nonneg.mpr
    (pow_le_one₀ inverse_history_discount_range.1.le inverse_history_discount_range.2.le)
  have hinit : (1-inverseHistoryDiscount^2)*(∑' j : ℕ,a j) ≤ (23/100:ℝ)*theta M := by
    have he : a=(fun j : ℕ => b*(inverseHistoryDiscount^(2*j)*bankDepthFrame M j*
        (∫ ω,cutoffTraceDefect M n (n-((5+j:ℕ):ℤ)) ω ∂μ))) := by
      funext j
      dsimp only [a]
      ring
    rw [he,tsum_mul_left]
    convert hi.2 using 1; ring
  have hde : (1-inverseHistoryDiscount^2)*(∑' j : ℕ,d j)=parentBoundaryWeakMeanSlope M.gamma height := hd.2
  have hscaled := mul_le_mul_of_nonneg_left hsum hdis
  rw [has.tsum_add (hds.mul_left t),tsum_mul_left] at hscaled
  refine ⟨hfs,?_⟩
  calc
    _ ≤ (1-inverseHistoryDiscount^2)*((∑' j : ℕ,a j)+t*(∑' j : ℕ,d j)) := hscaled
    _ = (1-inverseHistoryDiscount^2)*(∑' j : ℕ,a j)+t*((1-inverseHistoryDiscount^2)*(∑' j : ℕ,d j)) := by ring
    _ ≤ (23/100:ℝ)*theta M+t*parentBoundaryWeakMeanSlope M.gamma height := by
      rw [hde]
      exact add_le_add hinit le_rfl
    _ ≤ (23/100:ℝ)*theta M+t*(theta M*parentBoundaryWeakMeanSlope gammaZero height) :=
      add_le_add_right (mul_le_mul_of_nonneg_left (parent_boundary_weak_mean_slope_theta M hg height) ht.1) _
    _ = _ := by ring

end
end ASDExplicitGamma.Native
