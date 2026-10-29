module

public import ASDExplicitGamma.Cold.FiveSixthsBias
public import ASDExplicitGamma.Cold.MatrixFrobeniusTriangle

/-! # CO-COLD-FIVE-SIXTHS-CANDIDATE for actual source/parent responses -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Matrix
open scoped BigOperators ENNReal
namespace ASDExplicitGamma.Cold

/-- CO-COLD-FIVE-SIXTHS-CANDIDATE. The matrix fluctuation and scalar trace variance
are the source four-colour inputs, with e=2*3^(-d)*v_k and sigma=2*3^(-d)*L_k.
The actual response-gap bias and trace-square savings are derived internally. -/
theorem cold_five_sixths_candidate {Ω : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    [IsProbabilityMeasure ℙ] (A X : Ω → FullBlockMat 2) {p q r s D e σ : ℝ}
    (hA : ∀ i j, MemLp (fun ω => A ω i j) 2 ℙ)
    (hX : ∀ i j, MemLp (fun ω => X ω i j) 2 ℙ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hsub : ∀ᵐ ω ∂ℙ, (X ω-A ω).PosSemidef)
    (hTn : ∀ᵐ ω ∂ℙ, 0 ≤ (A ω).trace-4)
    (hmeanX : matrixMean ℙ X = 1+coldGraphBlockMean p q)
    (hmeanA : matrixMean ℙ A = 1+coldGraphBlockMean r s)
    (hD : 2*(p+q) ≤ D)
    (hcenter : matrixFrobeniusL2 ℙ (fun ω => X ω-matrixMean ℙ X) ≤ e)
    (hvariance : ProbabilityTheory.variance (fun ω => (X ω).trace-4) ℙ ≤ σ^2) :
    matrixFrobeniusL2 ℙ (fun ω => A ω-1) ≤ e+Real.sqrt ((5/6:ℝ)*D^2+σ^2) := by
  let Z := fun ω => X ω-A ω
  let P := coldGraphBlockMean p q
  let Q := coldGraphBlockMean r s
  let Y := fun ω => (X ω).trace-4
  let T := fun ω => (A ω).trace-4
  have hZ (i j) : MemLp (fun ω => Z ω i j) 2 ℙ := (hX i j).sub (hA i j)
  have hY : MemLp Y 2 ℙ := (memLp_finsetSum Finset.univ (fun i _ => hX i i)).sub (memLp_const 4)
  have hT : MemLp T 2 ℙ := (memLp_finsetSum Finset.univ (fun i _ => hA i i)).sub (memLp_const 4)
  have hZi : matrixMean ℙ Z = P-Q := by
    rw [matrixMean_sub X A (fun i j => (hX i j).integrable (by norm_num))
      (fun i j => (hA i j).integrable (by norm_num)),hmeanX,hmeanA]
    abel
  have htr : ∀ᵐ ω ∂ℙ, (Z ω).trace = Y ω-T ω := Filter.Eventually.of_forall (fun ω => by
    dsimp only [Z,Y,T]
    rw [Matrix.trace_sub]
    ring)
  have hTY : ∀ᵐ ω ∂ℙ, T ω ≤ Y ω := by
    filter_upwards [hsub,htr] with ω hω ht
    have hn := hω.trace_nonneg
    change 0 ≤ (Z ω).trace at hn
    rw [ht] at hn
    linarith only [hn]
  have hymean : (∫ ω, Y ω ∂ℙ) = 2*(p+q) := by
    dsimp only [Y]
    have hi : Integrable (fun ω => (X ω).trace) ℙ := integrable_finsetSum Finset.univ
      (fun i _ => (hX i i).integrable (by norm_num))
    rw [integral_sub hi (integrable_const 4),integral_matrix_trace X
      (fun i => (hX i i).integrable (by norm_num)),hmeanX,Matrix.trace_add,
      coldGraphBlockMean_trace,Matrix.trace_one,integral_const,probReal_univ,one_smul]
    norm_num [BlockCoord,Fintype.card_sum,Fintype.card_fin]
  have htmean : (∫ ω, T ω ∂ℙ) = 2*(r+s) := by
    dsimp only [T]
    have hi : Integrable (fun ω => (A ω).trace) ℙ := integrable_finsetSum Finset.univ
      (fun i _ => (hA i i).integrable (by norm_num))
    rw [integral_sub hi (integrable_const 4),integral_matrix_trace A
      (fun i => (hA i i).integrable (by norm_num)),hmeanA,Matrix.trace_add,
      coldGraphBlockMean_trace,Matrix.trace_one,integral_const,probReal_univ,one_smul]
    norm_num [BlockCoord,Fintype.card_sum,Fintype.card_fin]
  have hBias := cold_five_sixths_bias_bound hr hs hZ hY hT hsub htr hTn hTY hZi hymean htmean hvariance
  have hD2 := (sq_le_sq₀ (mul_nonneg (by norm_num) (add_nonneg hp hq))
    ((mul_nonneg (by norm_num) (add_nonneg hp hq)).trans hD)).mpr hD
  have hBiasD : (∫ ω, matrixFrobeniusSq (P-Z ω) ∂ℙ) ≤ (5/6:ℝ)*D^2+σ^2 := by
    linarith only [hBias,hD2]
  have hE (i j) : MemLp (fun ω => (X ω-matrixMean ℙ X) i j) 2 ℙ := (hX i j).sub (memLp_const _)
  have hPZ (i j) : MemLp (fun ω => (P-Z ω) i j) 2 ℙ := (memLp_const _).sub (hZ i j)
  have ht := matrixFrobeniusL2_add_le hE hPZ
  have heq : (fun ω => (X ω-matrixMean ℙ X)+(P-Z ω)) = (fun ω => A ω-1) := by
    funext ω
    rw [hmeanX]
    dsimp only [Z,P]
    abel
  rw [heq] at ht
  exact ht.trans (add_le_add hcenter (matrixFrobeniusL2_le_sqrt hBiasD))

end ASDExplicitGamma.Cold
