module

public import ASDExplicitGamma.Cold.PositiveFrobeniusTrace
public import ASDExplicitGamma.Cold.MatrixFrobeniusMoment
public import ASDExplicitGamma.Cold.GraphScalarAlgebra

/-! # The parent trace square retained by the five-sixths graph bound -/

@[expose] public section
noncomputable section
open MeasureTheory Matrix
open scoped ENNReal
namespace ASDExplicitGamma.Cold

/-- A positive response gap costs Y²-T², retaining the favorable parent-trace square. -/
theorem cold_graph_gap_frobenius_bound {n : Type*} [Fintype n] [DecidableEq n]
    {Z : Matrix n n ℝ} {Y T : ℝ} (hZ : Z.PosSemidef) (htrace : Z.trace = Y-T)
    (hT : 0 ≤ T) (hTY : T ≤ Y) : matrixFrobeniusSq Z ≤ Y^2-T^2 := by
  have h := matrixFrobeniusSq_le_trace_sq hZ
  rw [htrace] at h
  exact h.trans (cold_graph_trace_gap_square hT hTY)

/-- The exact trace variance cap and Jensen retain a²+variance-b² for the actual PSD gap. -/
theorem expected_cold_graph_gap_bound {Ω n : Type*} [MeasurableSpace Ω] [Fintype n] [DecidableEq n]
    {ℙ : Measure Ω} [IsProbabilityMeasure ℙ] {Z : Ω → Matrix n n ℝ} {Y T : Ω → ℝ}
    {a b σ : ℝ} (hZ : ∀ i j, MemLp (fun ω => Z ω i j) 2 ℙ)
    (hY : MemLp Y 2 ℙ) (hT : MemLp T 2 ℙ)
    (hpos : ∀ᵐ ω ∂ℙ, (Z ω).PosSemidef)
    (htrace : ∀ᵐ ω ∂ℙ, (Z ω).trace = Y ω-T ω)
    (hTn : ∀ᵐ ω ∂ℙ, 0 ≤ T ω) (hTY : ∀ᵐ ω ∂ℙ, T ω ≤ Y ω)
    (hmeanY : (∫ ω, Y ω ∂ℙ) = a) (hmeanT : (∫ ω, T ω ∂ℙ) = b)
    (hVar : ProbabilityTheory.variance Y ℙ ≤ σ^2) :
    (∫ ω, matrixFrobeniusSq (Z ω) ∂ℙ) ≤ a^2+σ^2-b^2 := by
  have hpoint : ∀ᵐ ω ∂ℙ, matrixFrobeniusSq (Z ω) ≤ Y ω^2-T ω^2 := by
    filter_upwards [hpos,htrace,hTn,hTY] with ω hp ht hn hb
    exact cold_graph_gap_frobenius_bound hp ht hn hb
  have h := integral_mono_ae (integrable_matrixFrobeniusSq hZ) (hY.integrable_sq.sub hT.integrable_sq) hpoint
  dsimp only [Pi.sub_apply] at h
  rw [integral_sub hY.integrable_sq hT.integrable_sq] at h
  have hYeq := ProbabilityTheory.variance_eq_sub hY
  have hTeq := ProbabilityTheory.variance_eq_sub hT
  have hTvar := ProbabilityTheory.variance_nonneg T ℙ
  dsimp only [Pi.pow_apply] at hYeq hTeq
  rw [hmeanY] at hYeq
  rw [hmeanT] at hTeq
  linarith only [h,hYeq,hTeq,hTvar,hVar]

end ASDExplicitGamma.Cold
