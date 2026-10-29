module

public import ASDExplicitGamma.Cold.NativeGraphCellCaps
public import ASDExplicitGamma.Cold.NativeOldGraph

/-! # The selected checked graph candidate for the actual native response -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Matrix Algsuperdiff.Section3
open scoped ENNReal
namespace ASDExplicitGamma.Cold
open ASDExplicitGamma.Numerics.Cold

/-- Every selected source graph candidate holds for the actual native fixed-frame matrix,
using only root input and means at genuinely earlier lags. -/
theorem cold_native_selected_graph (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (m : ℤ)
    {θ : ℝ} (hθ : 0 ≤ θ) (hroot : root20 M m ≤ ENNReal.ofReal (θ*(coldR20:ℝ)))
    {n ell : ℕ} (hn : n ≤ 128) (hell : ell < n) (hell126 : ell ≤ 126)
    (hmean : ∀ i < n, coldNativeMean M m i ≤ θ*(coldMeanAt i:ℝ)) :
    2*(∫ ω, matrixFrobeniusSq (coldNativeResponse M m (originCube 2 (m+(ell:ℤ))) ω-1)
      ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ coldSelectedGraphCap θ ell := by
  let Q := originCube 2 (m+(ell:ℤ))
  have hTA : MemLp (coldNativeCellTrace M m Q) 2 (Cutoff.cutoffSampleLaw M).toMeasure :=
    (coldNativeTrace_memLp hroot ell).mono_exponent (by norm_num)
  have hcaps (k : ℕ) (hk : k ≤ ell) := cold_native_graph_cell_caps M h hM m hθ hroot hn hell hell126 hk hmean
  have hscale {k : ℕ} (hk : k ≤ ell) : m ≤ Q.scale-((ell-k:ℕ):ℤ) := by
    change m ≤ m+(ell:ℤ)-((ell-k:ℕ):ℤ)
    omega
  have hk := cold_graph_choice_lag ell (List.mem_range.mpr (by omega))
  unfold coldSelectedGraphCap
  dsimp only
  split_ifs with hzero hodd
  · have hc := hcaps 0 (Nat.zero_le ell)
    have hm0 (C : SquareCells Q (ell-0)) :
        (∫ ω, coldNativeCellTrace M m C.val ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ θ*(coldA:ℝ) := by
      simpa only [cold_table_zero.1] using (hc C).2.1
    have hL0 (C : SquareCells Q (ell-0)) :
        lpNorm (coldNativeCellTrace M m C.val) 2 (Cutoff.cutoffSampleLaw M).toMeasure ≤ θ*(coldL0:ℝ) :=
      (hc C).2.2.trans (mul_le_mul_of_nonneg_left (Rat.cast_le.mpr cold_interpolation_zero_le_root) hθ)
    simpa only [Nat.sub_zero] using cold_native_graph_old M h hM m Q (ell-0) (hscale (Nat.zero_le ell))
      hTA (fun C => (hc C).1) hm0 hL0
  · have hc := hcaps _ hk.1
    exact cold_native_graph_five_sixths M h hM m Q _ (hscale hk.1)
      hTA (fun C => (hc C).1) (fun C => (hc C).2.1) (fun C => (hc C).2.2)
  · have hc := hcaps _ hk.2
    exact cold_native_graph_sandwich M h hM m Q _ (hscale hk.2)
      hTA (fun C => (hc C).1) (fun C => (hc C).2.1) (fun C => (hc C).2.2)

end ASDExplicitGamma.Cold
