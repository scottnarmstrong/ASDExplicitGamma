module

public import ASDExplicitGamma.Cold.GraphSandwichExpansion
public import ASDExplicitGamma.Cold.GraphReflectionMoment

/-! # VA-COLD-GRAPH: the actual annealed parent-from-children half-floor sandwich -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Matrix
open scoped ENNReal
namespace ASDExplicitGamma.Cold

/-- VA-COLD-GRAPH. Actual response positivity, inverse-reflection duality and matrix
subadditivity give the half-floor graph bound. The two expected scalar blocks may be
unequal. Every trace-product, centering and Cauchy--Schwarz step is proved internally. -/
theorem cold_graph_sandwich {Ω : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    [IsProbabilityMeasure ℙ] (A X : Ω → FullBlockMat 2) {p q r s : ℝ}
    (hA : ∀ i j, MemLp (fun ω => A ω i j) 2 ℙ)
    (hX : ∀ i j, MemLp (fun ω => X ω i j) 2 ℙ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) (hs : 0 ≤ s) (hrp : r ≤ p) (hsq : s ≤ q)
    (hpos : ∀ᵐ ω ∂ℙ, (A ω).PosDef)
    (hdual : ∀ᵐ ω ∂ℙ, (coarseGramSwap*A ω*coarseGramSwap-(A ω)⁻¹).PosSemidef)
    (hsub : ∀ᵐ ω ∂ℙ, (X ω-A ω).PosSemidef)
    (hmeanX : matrixMean ℙ X = 1+coldGraphBlockMean p q)
    (hmeanA : matrixMean ℙ A = 1+coldGraphBlockMean r s) :
    let e := matrixFrobeniusL2 ℙ (fun ω => X ω-matrixMean ℙ X)
    matrixFrobeniusL2 ℙ (fun ω => A ω-1) ≤ e+Real.sqrt ((2*(p+q))^2/2+2*e^2) := by
  dsimp only
  let P := coldGraphBlockMean p q
  let Q := coldGraphBlockMean r s
  let E := fun ω => X ω-matrixMean ℙ X
  let H := fun ω => A ω-1
  have hE (i j) : MemLp (fun ω => E ω i j) 2 ℙ := (hX i j).sub (memLp_const _)
  have hH (i j) : MemLp (fun ω => H ω i j) 2 ℙ := (hA i j).sub (memLp_const _)
  have hmeanE : matrixMean ℙ E = 0 := by
    rw [matrixMean_sub_const X (matrixMean ℙ X) (fun i j => (hX i j).integrable (by norm_num)),sub_self]
  have hmeanH : matrixMean ℙ H = Q := by
    rw [matrixMean_sub_const A (1:FullBlockMat 2) (fun i j => (hA i j).integrable (by norm_num)),hmeanA]
    dsimp only [Q]
    abel
  have heqU (ω : Ω) : P+E ω = X ω-1 := by
    dsimp only [P,E]
    rw [hmeanX]
    abel
  have hU (i j) : MemLp (fun ω => (P+E ω) i j) 2 ℙ := memLp_matrix_const_add P hE i j
  have hV (i j) : MemLp (fun ω => coldGraphReflection (P+E ω) i j) 2 ℙ := memLp_coldGraphReflection hU i j
  have hD (i j) : MemLp (fun ω => ((P+E ω)-coldGraphReflection (P+E ω)) i j) 2 ℙ :=
    (hU i j).sub (hV i j)
  have hpoint : ∀ᵐ ω ∂ℙ, matrixFrobeniusSq (H ω) ≤
      matrixFrobeniusInner ((P+E ω)-coldGraphReflection (P+E ω)) (H ω)+
      matrixFrobeniusInner (P+E ω) (coldGraphReflection (P+E ω)) := by
    filter_upwards [hpos,hdual,hsub] with ω hposω hdω hsω
    rw [heqU]
    exact cold_graph_source_sandwich hposω hsω hdω
  have hi1 := integrable_matrixFrobeniusInner hD hH
  have hi2 := integrable_matrixFrobeniusInner hU hV
  have h := integral_mono_ae (integrable_matrixFrobeniusSq hH) (hi1.add hi2) hpoint
  change (∫ ω, matrixFrobeniusSq (H ω) ∂ℙ) ≤
    ∫ ω, matrixFrobeniusInner ((P+E ω)-coldGraphReflection (P+E ω)) (H ω)+
      matrixFrobeniusInner (P+E ω) (coldGraphReflection (P+E ω)) ∂ℙ at h
  rw [integral_add (f := fun ω => matrixFrobeniusInner ((P+E ω)-coldGraphReflection (P+E ω)) (H ω))
    (g := fun ω => matrixFrobeniusInner (P+E ω) (coldGraphReflection (P+E ω))) hi1 hi2] at h
  change _ ≤ matrixFrobeniusPairing ℙ (fun ω => (P+E ω)-coldGraphReflection (P+E ω)) H+
    matrixFrobeniusPairing ℙ (fun ω => P+E ω) (fun ω => coldGraphReflection (P+E ω)) at h
  rw [cold_graph_sandwich_expansion P Q E H hE hH hmeanE hmeanH] at h
  have hdet := cold_graph_half_deterministic hp hq hr hs hrp hsq
  have hcross := coldGraphReflection_pairing_difference_le hE hH
  have hself := coldGraphReflection_pairing_self_le hE
  have hquad : (matrixFrobeniusL2 ℙ H)^2 ≤ (2*(p+q))^2/2+
      2*matrixFrobeniusL2 ℙ E*matrixFrobeniusL2 ℙ H+(matrixFrobeniusL2 ℙ E)^2 := by
    rw [matrixFrobeniusL2_sq]
    dsimp only [P,Q] at h
    linarith only [h,hdet,hcross,hself]
  exact cold_graph_sandwich_quadratic hquad

end ASDExplicitGamma.Cold
