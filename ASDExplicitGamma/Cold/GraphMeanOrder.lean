module

public import ASDExplicitGamma.Cold.MatrixMeanAlgebra
public import ASDExplicitGamma.Cold.ColdGraphBlocks

/-! # Scalar block order from the actual integrated response gap -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Matrix
open scoped ENNReal
namespace ASDExplicitGamma.Cold

/-- The actual source block mean has its precise scalar trace excess. -/
theorem cold_graph_mean_trace {Ω : Type*} [MeasurableSpace Ω] {μprob : Measure Ω}
    [IsProbabilityMeasure μprob] (A : Ω → FullBlockMat 2) {p q : ℝ}
    (hA : ∀ i, Integrable (fun ω => A ω i i) μprob)
    (hmean : matrixMean μprob A = 1+coldGraphBlockMean p q) :
    (∫ ω, (A ω).trace-4 ∂μprob) = 2*(p+q) := by
  have hi : Integrable (fun ω => (A ω).trace) μprob := integrable_finsetSum Finset.univ (fun i _ => hA i)
  rw [integral_sub hi (integrable_const 4),integral_matrix_trace A hA,hmean,Matrix.trace_add,
    coldGraphBlockMean_trace,Matrix.trace_one,integral_const,probReal_univ,one_smul]
  norm_num [BlockCoord,Fintype.card_sum,Fintype.card_fin]

/-- The actual PSD source gap orders both unequal scalar expectation blocks. -/
theorem cold_graph_mean_block_order {Ω : Type*} [MeasurableSpace Ω] {μprob : Measure Ω}
    [IsProbabilityMeasure μprob] (A X : Ω → FullBlockMat 2) {p q r s : ℝ}
    (hA : ∀ i j, MemLp (fun ω => A ω i j) 2 μprob)
    (hX : ∀ i j, MemLp (fun ω => X ω i j) 2 μprob)
    (hsub : ∀ᵐ ω ∂μprob, (X ω-A ω).PosSemidef)
    (hmeanX : matrixMean μprob X = 1+coldGraphBlockMean p q)
    (hmeanA : matrixMean μprob A = 1+coldGraphBlockMean r s) : r ≤ p ∧ s ≤ q := by
  have hd (i : BlockCoord 2) : (matrixMean μprob A) i i ≤ (matrixMean μprob X) i i := by
    apply integral_mono_ae ((hA i i).integrable (by norm_num)) ((hX i i).integrable (by norm_num))
    filter_upwards [hsub] with ω hω
    have hh := hω.diag_nonneg (i := i)
    exact sub_nonneg.mp hh
  have hp := hd (Sum.inl 0)
  have hq := hd (Sum.inr 0)
  rw [hmeanX,hmeanA] at hp hq
  simp only [coldGraphBlockMean,toFullBlockMat,Book.Ch02.blockDiag,Matrix.add_apply,
    Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,ite_true,mul_one] at hp hq
  constructor <;> linarith only [hp,hq]

end ASDExplicitGamma.Cold
