module

public import ASDExplicitGamma.Cold.MatrixMeanAlgebra
public import ASDExplicitGamma.Cold.ColdGraphBlocks
public import ASDExplicitGamma.Cold.GraphTraceGapMoment

/-! # The exact expected bias estimate behind the five-sixths graph candidate -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Matrix
open scoped ENNReal
namespace ASDExplicitGamma.Cold

/-- Retaining both favorable terms produces the exact five-sixths floor.
All random quantities are the actual PSD response gap and actual child/parent traces. -/
theorem cold_five_sixths_bias_bound {Ω : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    [IsProbabilityMeasure ℙ] {Z : Ω → FullBlockMat 2} {Y T : Ω → ℝ} {p q r s σ : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hZ : ∀ i j, MemLp (fun ω => Z ω i j) 2 ℙ) (hY : MemLp Y 2 ℙ) (hT : MemLp T 2 ℙ)
    (hpos : ∀ᵐ ω ∂ℙ, (Z ω).PosSemidef) (htrace : ∀ᵐ ω ∂ℙ, (Z ω).trace = Y ω-T ω)
    (hTn : ∀ᵐ ω ∂ℙ, 0 ≤ T ω) (hTY : ∀ᵐ ω ∂ℙ, T ω ≤ Y ω)
    (hmean : matrixMean ℙ Z = coldGraphBlockMean p q-coldGraphBlockMean r s)
    (hmeanY : (∫ ω, Y ω ∂ℙ) = 2*(p+q)) (hmeanT : (∫ ω, T ω ∂ℙ) = 2*(r+s))
    (hVar : ProbabilityTheory.variance Y ℙ ≤ σ^2) :
    (∫ ω, matrixFrobeniusSq (coldGraphBlockMean p q-Z ω) ∂ℙ) ≤
      (5/6:ℝ)*(2*(p+q))^2+σ^2 := by
  rw [integral_matrixFrobeniusSq_bias_gap hZ hmean,
    coldGraphBlockMean_frobenius,coldGraphBlockMean_inner]
  have hgap := expected_cold_graph_gap_bound hZ hY hT hpos htrace hTn hTY hmeanY hmeanT hVar
  have hcross := cold_graph_cross_bias (p := p) (q := q) hr hs
  have hmax := cold_graph_fiveSixths_max (2*(p+q)) (2*(r+s))
  linarith only [hgap,hcross,hmax]

end ASDExplicitGamma.Cold
