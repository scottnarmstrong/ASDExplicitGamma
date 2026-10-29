module

public import ASDExplicitGamma.Cold.NativeGraphData
public import ASDExplicitGamma.Cold.FiveSixthsCandidate
public import ASDExplicitGamma.Cold.GraphSandwichCandidate
public import ASDExplicitGamma.Cold.ColdGraphAnalytic

/-! # The improved graph candidates for the actual native fixed model -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Matrix Algsuperdiff.Section3
open scoped ENNReal
namespace ASDExplicitGamma.Cold

/-- The exact five-sixths candidate for the actual native response, with every graph input produced. -/
theorem cold_native_graph_five_sixths (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (Q : TriadicCube 2) (depth : ℕ) (hm : m ≤ Q.scale-(depth:ℤ)) {D L : ℝ}
    (hTA : MemLp (coldNativeCellTrace M m Q) 2 (Cutoff.cutoffSampleLaw M).toMeasure)
    (hT : ∀ C : SquareCells Q depth, MemLp (coldNativeCellTrace M m C.val) 2 (Cutoff.cutoffSampleLaw M).toMeasure)
    (hD : ∀ C : SquareCells Q depth, (∫ ω, coldNativeCellTrace M m C.val ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ D)
    (hL : ∀ C : SquareCells Q depth, lpNorm (coldNativeCellTrace M m C.val) 2 (Cutoff.cutoffSampleLaw M).toMeasure ≤ L) :
    2*(∫ ω, matrixFrobeniusSq (coldNativeResponse M m Q ω-1) ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      coldFiveSixthsGraphCap D L depth := by
  let G := coldNativeGraphData M h hM m Q depth hm hTA hT hD hL
  have hh := cold_five_sixths_candidate (coldNativeResponse M m Q) (coldNativeResponseAverage M m Q depth)
    G.hA G.hX G.hp G.hq G.hr G.hs
    (Filter.Eventually.of_forall (coldNativeResponseAverage_subadditive M m Q depth))
    (Filter.Eventually.of_forall (fun ω => by rw [coldNativeResponse_trace]; exact coldNativeCellTrace_nonneg M m Q ω))
    G.hmeanX G.hmeanA G.hD G.hcenter G.hvariance
  have hn : 0 ≤ matrixFrobeniusL2 (Cutoff.cutoffSampleLaw M).toMeasure (fun ω => coldNativeResponse M m Q ω-1) :=
    Real.sqrt_nonneg _
  have hs := (sq_le_sq₀ hn (hn.trans hh)).mpr hh
  rw [matrixFrobeniusL2_sq] at hs
  unfold coldFiveSixthsGraphCap
  dsimp only
  have he : (2*(3:ℝ)^(-(depth:ℝ))*L)^2 = (2*(3:ℝ)^(-(depth:ℝ)))^2*L^2 := by ring
  rw [he] at hs
  linarith only [hs]

/-- The exact half-floor candidate for the actual native response, with block order derived. -/
theorem cold_native_graph_sandwich (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (m : ℤ) (Q : TriadicCube 2) (depth : ℕ) (hm : m ≤ Q.scale-(depth:ℤ)) {D L : ℝ}
    (hTA : MemLp (coldNativeCellTrace M m Q) 2 (Cutoff.cutoffSampleLaw M).toMeasure)
    (hT : ∀ C : SquareCells Q depth, MemLp (coldNativeCellTrace M m C.val) 2 (Cutoff.cutoffSampleLaw M).toMeasure)
    (hD : ∀ C : SquareCells Q depth, (∫ ω, coldNativeCellTrace M m C.val ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ D)
    (hL : ∀ C : SquareCells Q depth, lpNorm (coldNativeCellTrace M m C.val) 2 (Cutoff.cutoffSampleLaw M).toMeasure ≤ L) :
    2*(∫ ω, matrixFrobeniusSq (coldNativeResponse M m Q ω-1) ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      coldSandwichGraphCap D L depth := by
  let G := coldNativeGraphData M h hM m Q depth hm hTA hT hD hL
  have hsub : ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      (coldNativeResponseAverage M m Q depth ω-coldNativeResponse M m Q ω).PosSemidef := Filter.Eventually.of_forall (coldNativeResponseAverage_subadditive M m Q depth)
  have ho := cold_graph_mean_block_order _ _ G.hA G.hX hsub G.hmeanX G.hmeanA
  exact cold_graph_sandwich_candidate _ _ depth G.hA G.hX G.hp G.hq G.hr G.hs ho.1 ho.2
    (Filter.Eventually.of_forall (coldNativeResponse_posDef M m Q))
    (Filter.Eventually.of_forall (coldNativeResponse_duality M m Q)) hsub G.hmeanX G.hmeanA G.hD G.hcenter

end ASDExplicitGamma.Cold
