module

public import ASDExplicitGamma.Cold.NativeGraphCandidates
public import ASDExplicitGamma.Cold.ColdGraphTable

/-! # Strictly earlier native scalar caps on the actual graph source cells -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Algsuperdiff.Section3
open scoped ENNReal
namespace ASDExplicitGamma.Cold
open ASDExplicitGamma.Numerics.Cold

/-- The root interpolation table is no larger than the root L2 endpoint. -/
theorem cold_interpolation_zero_le_root : coldInterpolationAt 0 ≤ coldL0 := by decide +kernel

/-- Actual graph source cells inherit all scalar inputs from their strictly earlier native lag. -/
theorem cold_native_graph_cell_caps (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (m : ℤ)
    {θ : ℝ} (hθ : 0 ≤ θ) (hroot : root20 M m ≤ ENNReal.ofReal (θ*(coldR20:ℝ)))
    {n ell k : ℕ} (hn : n ≤ 128) (hell : ell < n) (hell126 : ell ≤ 126) (hk : k ≤ ell)
    (hmean : ∀ i < n, coldNativeMean M m i ≤ θ*(coldMeanAt i:ℝ)) :
    ∀ C : SquareCells (originCube 2 (m+(ell:ℤ))) (ell-k),
      MemLp (coldNativeCellTrace M m C.val) 2 (Cutoff.cutoffSampleLaw M).toMeasure ∧
      (∫ ω, coldNativeCellTrace M m C.val ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ θ*(coldMeanAt k:ℝ) ∧
      lpNorm (coldNativeCellTrace M m C.val) 2 (Cutoff.cutoffSampleLaw M).toMeasure ≤ θ*(coldInterpolationAt k:ℝ) := by
  intro C
  have hc : C.val.scale = m+(k:ℤ) := by
    have hh := scale_eq_sub_of_mem_descendantsAtDepth C.property
    change C.val.scale = m+(ell:ℤ)-((ell-k:ℕ):ℤ) at hh
    omega
  have hT : MemLp (coldNativeTrace M m k) 2 (Cutoff.cutoffSampleLaw M).toMeasure :=
    (coldNativeTrace_memLp hroot k).mono_exponent (by norm_num)
  refine ⟨?_,?_,?_⟩
  · apply (coldNativeCellTrace_memLp_iff M m C.val 2).mpr
    rw [hc]
    exact hT
  · rw [coldNativeCellTrace_integral,hc]
    exact hmean k (hk.trans_lt hell)
  · rw [coldNativeCellTrace_norm,hc]
    exact cold_native_raw_interpolation M h hM m hθ hroot hn (hk.trans_lt hell) (hk.trans hell126) hmean

end ASDExplicitGamma.Cold
