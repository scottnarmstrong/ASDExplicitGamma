module

public import ASDExplicitGamma.Cold.ColdGraphSandwich

/-! # CO-GRAPH-SANDWICH: the source in-grid half-floor graph candidate -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Matrix
namespace ASDExplicitGamma.Cold

/-- CO-GRAPH-SANDWICH. At source separation d=ell-k, the source centered four-colour
cap and actual mean cap give the displayed actual twice-Frobenius-square graph bound.
The exact identity with matched four-load graph energy is in `MatchedGraphIdentity`. -/
theorem cold_graph_sandwich_candidate {Ω : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    [IsProbabilityMeasure ℙ] (A X : Ω → FullBlockMat 2) {p q r s D L : ℝ} (d : ℕ)
    (hA : ∀ i j, MemLp (fun ω => A ω i j) 2 ℙ)
    (hX : ∀ i j, MemLp (fun ω => X ω i j) 2 ℙ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) (hs : 0 ≤ s) (hrp : r ≤ p) (hsq : s ≤ q)
    (hpos : ∀ᵐ ω ∂ℙ, (A ω).PosDef)
    (hdual : ∀ᵐ ω ∂ℙ, (coarseGramSwap*A ω*coarseGramSwap-(A ω)⁻¹).PosSemidef)
    (hsub : ∀ᵐ ω ∂ℙ, (X ω-A ω).PosSemidef)
    (hmeanX : matrixMean ℙ X = 1+coldGraphBlockMean p q)
    (hmeanA : matrixMean ℙ A = 1+coldGraphBlockMean r s)
    (hD : 2*(p+q) ≤ D)
    (hcenter : matrixFrobeniusL2 ℙ (fun ω => X ω-matrixMean ℙ X) ≤
      2*(3:ℝ)^(-(d:ℝ))*Real.sqrt (2*D+L^2)) :
    let e := 2*(3:ℝ)^(-(d:ℝ))*Real.sqrt (2*D+L^2)
    2*(∫ ω, matrixFrobeniusSq (A ω-1) ∂ℙ) ≤ 2*(e+Real.sqrt (D^2/2+2*e^2))^2 := by
  dsimp only
  let e := matrixFrobeniusL2 ℙ (fun ω => X ω-matrixMean ℙ X)
  let cap := 2*(3:ℝ)^(-(d:ℝ))*Real.sqrt (2*D+L^2)
  have he : 0 ≤ e := Real.sqrt_nonneg _
  have hc : 0 ≤ cap := he.trans hcenter
  have ha : 0 ≤ 2*(p+q) := mul_nonneg (by norm_num) (add_nonneg hp hq)
  have hD0 : 0 ≤ D := ha.trans hD
  have he2 := (sq_le_sq₀ he hc).mpr hcenter
  have ha2 := (sq_le_sq₀ ha hD0).mpr hD
  have hrad : Real.sqrt ((2*(p+q))^2/2+2*e^2) ≤ Real.sqrt (D^2/2+2*cap^2) := by
    apply Real.sqrt_le_sqrt
    linarith only [he2,ha2]
  have h := cold_graph_sandwich A X hA hX hp hq hr hs hrp hsq hpos hdual hsub hmeanX hmeanA
  change matrixFrobeniusL2 ℙ (fun ω => A ω-1) ≤ e+Real.sqrt ((2*(p+q))^2/2+2*e^2) at h
  have hb := h.trans (add_le_add hcenter hrad)
  have hn : 0 ≤ matrixFrobeniusL2 ℙ (fun ω => A ω-1) := Real.sqrt_nonneg _
  have hsq := (sq_le_sq₀ hn (hn.trans hb)).mpr hb
  rw [matrixFrobeniusL2_sq] at hsq
  linarith only [hsq]

end ASDExplicitGamma.Cold
