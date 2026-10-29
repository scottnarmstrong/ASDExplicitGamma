module

public import ASDExplicitGamma.Cold.FiniteSpectralPair
public import ASDExplicitGamma.Cold.LpMonotonicity
public import ASDExplicitGamma.Cold.ColdGraphBlocks
public import ASDExplicitGamma.Cold.PositiveFrobeniusTrace
public import ASDExplicitGamma.Cold.MatrixFrobeniusTriangle

/-! # The decay and global candidates of CO-COLD-OLD-GRAPH-CAP -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Matrix
open scoped BigOperators ENNReal
namespace ASDExplicitGamma.Cold

/-- A constant response bias has its actual ordinary Frobenius norm in probability. -/
theorem matrixFrobeniusL2_const {Ω n : Type*} [MeasurableSpace Ω] [Fintype n]
    (ℙ : Measure Ω) [IsProbabilityMeasure ℙ] (P : Matrix n n ℝ) :
    matrixFrobeniusL2 ℙ (fun _ : Ω => P) = Real.sqrt (matrixFrobeniusSq P) := by
  unfold matrixFrobeniusL2
  rw [integral_const,probReal_univ,one_smul]

/-- The source old graph decay bound for actual parent and source-average matrices. -/
theorem cold_old_graph_decay {Ω : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    [IsProbabilityMeasure ℙ] (A X : Ω → FullBlockMat 2) {p q a e σ : ℝ}
    (hA : ∀ i j, MemLp (fun ω => A ω i j) 2 ℙ)
    (hX : ∀ i j, MemLp (fun ω => X ω i j) 2 ℙ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (ha : 2*(p+q) ≤ a)
    (hsub : ∀ᵐ ω ∂ℙ, (X ω-A ω).PosSemidef)
    (hTn : ∀ᵐ ω ∂ℙ, 0 ≤ (A ω).trace-4)
    (hmeanX : matrixMean ℙ X = 1+coldGraphBlockMean p q)
    (hcenter : matrixFrobeniusL2 ℙ (fun ω => X ω-matrixMean ℙ X) ≤ e)
    (htrace : lpNorm (fun ω => (X ω).trace-4) 2 ℙ ≤ a+σ) :
    matrixFrobeniusL2 ℙ (fun ω => A ω-1) ≤ 2*a+e+σ := by
  let Z := fun ω => X ω-A ω
  let P := coldGraphBlockMean p q
  let Y := fun ω => (X ω).trace-4
  have hZ (i j) : MemLp (fun ω => Z ω i j) 2 ℙ := (hX i j).sub (hA i j)
  have hY : MemLp Y 2 ℙ := (memLp_finsetSum Finset.univ (fun i _ => hX i i)).sub (memLp_const 4)
  have hpoint : ∀ᵐ ω ∂ℙ, matrixFrobeniusSq (Z ω) ≤ Y ω^2 := by
    filter_upwards [hsub,hTn] with ω hz ht
    have htrace : (Z ω).trace ≤ Y ω := by
      dsimp only [Z,Y]
      rw [Matrix.trace_sub]
      linarith only [ht]
    exact (matrixFrobeniusSq_le_trace_sq hz).trans
      ((sq_le_sq₀ hz.trace_nonneg (hz.trace_nonneg.trans htrace)).mpr htrace)
  have hgap := integral_mono_ae (integrable_matrixFrobeniusSq hZ) hY.integrable_sq hpoint
  have he : matrixFrobeniusL2 ℙ Z ≤ lpNorm Y 2 ℙ := by
    have hnorm := lpNorm_eq_integral_norm_rpow_toReal (by norm_num : (2:ℝ≥0∞) ≠ 0)
      (by norm_num : (2:ℝ≥0∞) ≠ ⊤) hY.aestronglyMeasurable
    norm_num only [ENNReal.toReal_ofNat,Real.rpow_ofNat] at hnorm
    simp only [Real.norm_eq_abs,sq_abs] at hnorm
    rw [hnorm,← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_sqrt hgap
  have ha0 : 0 ≤ a := (mul_nonneg (by norm_num) (add_nonneg hp hq)).trans ha
  have hP : matrixFrobeniusL2 ℙ (fun _ : Ω => P) ≤ a := by
    rw [matrixFrobeniusL2_const,coldGraphBlockMean_frobenius]
    apply (Real.sqrt_le_iff).mpr
    refine ⟨ha0,?_⟩
    have hm := (sq_le_sq₀ (mul_nonneg (by norm_num) (add_nonneg hp hq)) ha0).mpr ha
    nlinarith only [hm,mul_nonneg hp hq,sq_nonneg p,sq_nonneg q]
  have hnegZ : matrixFrobeniusL2 ℙ (fun ω => -Z ω) = matrixFrobeniusL2 ℙ Z := by
    unfold matrixFrobeniusL2 matrixFrobeniusSq
    simp only [Matrix.neg_apply,neg_sq]
  have hNZ (i j) : MemLp (fun ω => (-Z ω) i j) 2 ℙ := (hZ i j).neg
  have hpz := matrixFrobeniusL2_add_le (fun i j => (memLp_const (P i j) : MemLp (fun _ : Ω => P i j) 2 ℙ))
    hNZ
  rw [hnegZ] at hpz
  have hE (i j) : MemLp (fun ω => (X ω-matrixMean ℙ X) i j) 2 ℙ := (hX i j).sub (memLp_const _)
  have hPZ (i j) : MemLp (fun ω => (P-Z ω) i j) 2 ℙ := (memLp_const _).sub (hZ i j)
  have ht := matrixFrobeniusL2_add_le hE hPZ
  have heq : (fun ω => (X ω-matrixMean ℙ X)+(P-Z ω)) = (fun ω => A ω-1) := by
    funext ω
    rw [hmeanX]
    dsimp only [P,Z]
    abel
  rw [heq] at ht
  have hpzeq : (fun ω => P+ -Z ω) = (fun ω => P-Z ω) := by funext ω; abel
  rw [hpzeq] at hpz
  linarith only [ht,hcenter,hpz,hP,he,htrace]

end ASDExplicitGamma.Cold
