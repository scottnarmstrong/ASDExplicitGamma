module

public import ASDExplicitGamma.Cold.OldGraphCandidate

/-! # The global trace branch of the source old-graph cap -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Matrix
open scoped BigOperators ENNReal
namespace ASDExplicitGamma.Cold

/-- Actual spectral duality yields the source global graph cap without a graph hypothesis. -/
theorem cold_old_graph_global {Ω : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    [IsProbabilityMeasure ℙ] (A : Ω → FullBlockMat 2) {a L : ℝ}
    (hA : ∀ i j, MemLp (fun ω => A ω i j) 2 ℙ)
    (hpos : ∀ᵐ ω ∂ℙ, (A ω).PosDef)
    (hdual : ∀ᵐ ω ∂ℙ, (coarseGramSwap*A ω*coarseGramSwap-(A ω)⁻¹).PosSemidef)
    (hmean : (∫ ω, (A ω).trace-4 ∂ℙ) ≤ a)
    (htrace : lpNorm (fun ω => (A ω).trace-4) 2 ℙ ≤ L) :
    2*(∫ ω, matrixFrobeniusSq (A ω-1) ∂ℙ) ≤ 4*(a+L^2) := by
  let T := fun ω => (A ω).trace-4
  have hT : MemLp T 2 ℙ := (memLp_finsetSum Finset.univ (fun i _ => hA i i)).sub (memLp_const 4)
  have hTi := hT.integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)
  have hdiff (i j) : MemLp (fun ω => (A ω-1) i j) 2 ℙ := (hA i j).sub (memLp_const _)
  have hpoint : ∀ᵐ ω ∂ℙ, matrixFrobeniusSq (A ω-1) ≤ 2*T ω+T ω^2 := by
    filter_upwards [hpos,hdual] with ω hp hd
    exact (matrix_spectral_pair_finite (d := 2) (by simp [BlockCoord]) (A ω) coarseGramSwap hp
      coarseGramSwap_isHermitian coarseGramSwap_sq hd).2
  have h := integral_mono_ae (integrable_matrixFrobeniusSq hdiff)
    ((hTi.const_mul 2).add hT.integrable_sq) hpoint
  dsimp only [Pi.add_apply] at h
  rw [integral_add (f := fun ω => 2*T ω) (g := fun ω => T ω^2) (hTi.const_mul 2) hT.integrable_sq,
    integral_const_mul] at h
  have hnorm : lpNorm T 2 ℙ = Real.sqrt (∫ ω, T ω^2 ∂ℙ) := by
    rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num : (2:ℝ≥0∞) ≠ 0)
      (by norm_num : (2:ℝ≥0∞) ≠ ⊤) hT.aestronglyMeasurable]
    norm_num only [ENNReal.toReal_ofNat,Real.rpow_ofNat]
    simp only [Real.norm_eq_abs,sq_abs,Real.sqrt_eq_rpow]
  have hsq : (∫ ω, T ω^2 ∂ℙ) ≤ L^2 := by
    have hL : 0 ≤ L := lpNorm_nonneg.trans htrace
    have hs := (sq_le_sq₀ (lpNorm_nonneg (f := T) (p := 2) (μ := ℙ)) hL).mpr htrace
    rw [hnorm,Real.sq_sqrt (integral_nonneg (fun ω => sq_nonneg (T ω)))] at hs
    exact hs
  change (∫ ω, T ω ∂ℙ) ≤ a at hmean
  linarith only [h,hmean,hsq,sq_nonneg L]

/-- CO-COLD-OLD-GRAPH-CAP: the exact minimum of the source decay and global branches.
The graph is the actual twice-Frobenius-square observable, whose optimizer identity
is proved separately in `MatchedGraphIdentity`. -/
theorem cold_old_graph_cap {Ω : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    [IsProbabilityMeasure ℙ] (A X : Ω → FullBlockMat 2) {p q a L : ℝ} (ℓ : ℕ)
    (hA : ∀ i j, MemLp (fun ω => A ω i j) 2 ℙ)
    (hX : ∀ i j, MemLp (fun ω => X ω i j) 2 ℙ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (ha : 2*(p+q) ≤ a)
    (hsub : ∀ᵐ ω ∂ℙ, (X ω-A ω).PosSemidef)
    (hpos : ∀ᵐ ω ∂ℙ, (A ω).PosDef)
    (hdual : ∀ᵐ ω ∂ℙ, (coarseGramSwap*A ω*coarseGramSwap-(A ω)⁻¹).PosSemidef)
    (hmeanX : matrixMean ℙ X = 1+coldGraphBlockMean p q)
    (hmeanA : (∫ ω, (A ω).trace-4 ∂ℙ) ≤ a)
    (htraceA : lpNorm (fun ω => (A ω).trace-4) 2 ℙ ≤ L)
    (hcenter : matrixFrobeniusL2 ℙ (fun ω => X ω-matrixMean ℙ X) ≤
      2*(3:ℝ)^(-(ℓ:ℝ))*Real.sqrt (2*a+L^2))
    (htraceX : lpNorm (fun ω => (X ω).trace-4) 2 ℙ ≤ a+2*(3:ℝ)^(-(ℓ:ℝ))*L) :
    2*(∫ ω, matrixFrobeniusSq (A ω-1) ∂ℙ) ≤
      min (2*(2*a+2*(Real.sqrt (2*a+L^2)+L)*(3:ℝ)^(-(ℓ:ℝ)))^2) (4*(a+L^2)) := by
  have hTn : ∀ᵐ ω ∂ℙ, 0 ≤ (A ω).trace-4 := by
    filter_upwards [hpos,hdual] with ω hp hd
    exact (matrix_spectral_pair_finite (d := 2) (by simp [BlockCoord]) (A ω) coarseGramSwap hp
      coarseGramSwap_isHermitian coarseGramSwap_sq hd).1
  have hdecay := cold_old_graph_decay A X hA hX hp hq ha hsub hTn hmeanX hcenter htraceX
  have heq : 2*a+2*(3:ℝ)^(-(ℓ:ℝ))*Real.sqrt (2*a+L^2)+2*(3:ℝ)^(-(ℓ:ℝ))*L =
      2*a+2*(Real.sqrt (2*a+L^2)+L)*(3:ℝ)^(-(ℓ:ℝ)) := by ring
  rw [heq] at hdecay
  apply le_min
  · have hn : 0 ≤ matrixFrobeniusL2 ℙ (fun ω => A ω-1) := Real.sqrt_nonneg _
    have hs := (sq_le_sq₀ hn (hn.trans hdecay)).mpr hdecay
    rw [matrixFrobeniusL2_sq] at hs
    linarith only [hs]
  · exact cold_old_graph_global A hA hpos hdual hmeanA htraceA

end ASDExplicitGamma.Cold
