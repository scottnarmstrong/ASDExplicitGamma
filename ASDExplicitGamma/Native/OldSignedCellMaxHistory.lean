module

public import ASDExplicitGamma.Native.OldSignedMaxHistoryAffine

/-! The OLD maximum-history estimate on every cell of the source mesh. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Gaussian Scalar Inverse Cold Main Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- Population payment on an arbitrary cell at the source scale. Stationarity
is used only for individual depth marks, without independence of the maxima. -/
theorem old_signed_cell_depth_max_L20_bound
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hgamma : M.gamma ≤ gammaZero) (m : ℤ)
    (hpast : ∀ n ≤ m, nativeInductionState M h n)
    (Q : TriadicCube 2) (hQ : Q.scale = m - 5)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (j : ℕ) :
    eLpNorm (mainOrdinaryTraceDepthMax M m Q t j)
        20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ((9 : ℝ≥0∞) ^ j) ^ (1 / 20 : ℝ) *
        ENNReal.ofReal (lpNorm
          (rawDepthFourLoadTrace M m (m - ((5 + j : ℕ) : ℤ)) t)
          20 (Cutoff.cutoffSampleLaw M).toMeasure) := by
  let μ := (Cutoff.cutoffSampleLaw M).toMeasure
  let s := descendantsAtDepth Q j
  have hOrigin : MemLp
      (rawDepthFourLoadTrace M m (m - ((5 + j : ℕ) : ℤ)) t) 20 μ := by
    exact main_rawDepthFourLoadTrace_memLp_twenty_fixed_old_frame
      M h hM hgamma m hpast j t ⟨ht0, ht1⟩
  have hcell (V : TriadicCube 2) (hV : V ∈ s) :
      MemLp (rawCubeFourLoadTrace M m V t) 20 μ := by
    have hscale : V.scale = m - ((5 + j : ℕ) : ℤ) := by
      rw [scale_eq_sub_of_mem_descendantsAtDepth hV, hQ]
      omega
    have hOriginV : MemLp (rawDepthFourLoadTrace M m V.scale t) 20 μ := by
      simpa only [hscale] using hOrigin
    exact main_rawCubeFourLoadTrace_memLp_of_origin M m V t 20 hOriginV
  have hnorm (V : TriadicCube 2) (hV : V ∈ s) :
      eLpNorm (fun ω => ENNReal.ofReal (rawCubeFourLoadTrace M m V t ω))
          20 μ ≤
        ENNReal.ofReal (lpNorm
          (rawDepthFourLoadTrace M m (m - ((5 + j : ℕ) : ℤ)) t) 20 μ) := by
    have hnonneg (ω : Cutoff.CutoffSample 2) :
        0 ≤ rawCubeFourLoadTrace M m V t ω :=
      raw_cube_four_load_trace_nonneg M m V t ⟨ht0, ht1⟩ ω
    have hto :
        (fun ω => ENNReal.ofReal (rawCubeFourLoadTrace M m V t ω)) =
          fun ω => ‖rawCubeFourLoadTrace M m V t ω‖ₑ := by
      funext ω
      exact (Real.enorm_eq_ofReal (hnonneg ω)).symm
    rw [hto, eLpNorm_enorm _ (hcell V hV).aestronglyMeasurable]
    apply le_of_eq
    have hscale : V.scale = m - ((5 + j : ℕ) : ℤ) := by
      rw [scale_eq_sub_of_mem_descendantsAtDepth hV, hQ]
      omega
    calc
      _ = ENNReal.ofReal
          (lpNorm (rawCubeFourLoadTrace M m V t) 20 μ) := by
            rw [← ENNReal.ofReal_toReal (hcell V hV).eLpNorm_ne_top]
            rfl
      _ = ENNReal.ofReal
          (lpNorm (rawDepthFourLoadTrace M m
            (m - ((5 + j : ℕ) : ℤ)) t) 20 μ) := by
            have hOriginV : MemLp (rawDepthFourLoadTrace M m V.scale t) 20 μ := by
              simpa only [hscale] using hOrigin
            have hnormeq := main_rawCubeFourLoadTrace_lpNorm_eq_origin
              M m V t 20 hOriginV
            simpa only [hscale] using congrArg ENNReal.ofReal hnormeq
  have hmax := history_finite_max_L20 μ s
    (fun V ω => ENNReal.ofReal (rawCubeFourLoadTrace M m V t ω))
    (fun V => by
      have hm := main_ordinary_trace_depth_max_measurable M m V t 0
      change Measurable (fun ω => (descendantsAtDepth V 0).sup
        (fun W => ENNReal.ofReal (rawCubeFourLoadTrace M m W t ω))) at hm
      simpa only [descendantsAtDepth_zero, Finset.sup_singleton] using hm)
    (ENNReal.ofReal (lpNorm
      (rawDepthFourLoadTrace M m (m - ((5 + j : ℕ) : ℤ)) t) 20 μ)) hnorm
  have hcard : (s.card : ℝ≥0∞) = (9 : ℝ≥0∞) ^ j := by
    dsimp [s]
    rw [descendantsAtDepth_card]
    norm_num
  simpa only [mainOrdinaryTraceDepthMax, hcard] using hmax


end
end ASDExplicitGamma.Native
