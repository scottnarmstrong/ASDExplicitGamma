module

public import ASDExplicitGamma.Cold.ColdGraphReflection
public import ASDExplicitGamma.Cold.MatrixFrobeniusTriangle
public import ASDExplicitGamma.Cold.MatrixFrobeniusPairing

/-! # Sharp matrix fluctuation bounds for the actual block reflection -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Matrix
namespace ASDExplicitGamma.Cold

/-- Reflection subtraction costs at most twice the actual centered matrix norm. -/
theorem coldGraphReflection_difference_L2 {Ω : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    {E : Ω → FullBlockMat 2} (hE : ∀ i j, MemLp (fun ω => E ω i j) 2 ℙ) :
    matrixFrobeniusL2 ℙ (fun ω => E ω-coldGraphReflection (E ω)) ≤ 2*matrixFrobeniusL2 ℙ E := by
  have hneg (i j) : MemLp (fun ω => (-coldGraphReflection (E ω)) i j) 2 ℙ :=
    (memLp_coldGraphReflection hE i j).neg
  have h := matrixFrobeniusL2_add_le hE hneg
  have hn : matrixFrobeniusL2 ℙ (fun ω => -coldGraphReflection (E ω)) =
      matrixFrobeniusL2 ℙ (fun ω => coldGraphReflection (E ω)) := by
    unfold matrixFrobeniusL2 matrixFrobeniusSq
    simp only [Matrix.neg_apply,neg_sq]
  rw [hn,coldGraphReflection_L2] at h
  have he : (fun ω => E ω+ -coldGraphReflection (E ω)) = (fun ω => E ω-coldGraphReflection (E ω)) := by
    funext ω
    abel
  rw [he] at h
  linarith only [h]

/-- The actual centered-reflected cross term costs at most e². -/
theorem coldGraphReflection_pairing_self_le {Ω : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    {E : Ω → FullBlockMat 2} (hE : ∀ i j, MemLp (fun ω => E ω i j) 2 ℙ) :
    matrixFrobeniusPairing ℙ E (fun ω => coldGraphReflection (E ω)) ≤ (matrixFrobeniusL2 ℙ E)^2 := by
  have h := (le_abs_self _).trans (abs_integral_matrixFrobeniusInner_le hE (memLp_coldGraphReflection hE))
  rw [coldGraphReflection_L2] at h
  exact h.trans_eq (pow_two _).symm

/-- The actual antisymmetric-reflection cross term costs at most 2e*sqrt(W). -/
theorem coldGraphReflection_pairing_difference_le {Ω : Type*} [MeasurableSpace Ω] {ℙ : Measure Ω}
    {E H : Ω → FullBlockMat 2} (hE : ∀ i j, MemLp (fun ω => E ω i j) 2 ℙ)
    (hH : ∀ i j, MemLp (fun ω => H ω i j) 2 ℙ) :
    matrixFrobeniusPairing ℙ (fun ω => E ω-coldGraphReflection (E ω)) H ≤
      2*matrixFrobeniusL2 ℙ E*matrixFrobeniusL2 ℙ H := by
  have hd (i j) : MemLp (fun ω => (E ω-coldGraphReflection (E ω)) i j) 2 ℙ :=
    (hE i j).sub (memLp_coldGraphReflection hE i j)
  have h := (le_abs_self _).trans (abs_integral_matrixFrobeniusInner_le hd hH)
  exact h.trans (mul_le_mul_of_nonneg_right (coldGraphReflection_difference_L2 hE) (Real.sqrt_nonneg _))

end ASDExplicitGamma.Cold
