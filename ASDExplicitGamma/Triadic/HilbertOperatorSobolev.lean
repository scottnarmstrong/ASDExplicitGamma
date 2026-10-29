module

public import ASDExplicitGamma.Triadic.HilbertL2Bounds
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! Genuine weak W^{1,∞} operator fields and their evaluated Hilbert H1 fields. -/

@[expose] public section
namespace ASDExplicitGamma.Triadic
open Homogenization MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

/-- An operator-valued W^{1,∞} field, characterized by its actual weak derivatives
against fixed input vectors and scalar Hilbert functionals. -/
structure HilbertOperatorW1Infinity {d : ℕ} (Q : TriadicCube d) (E F : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] where
  toFun : Vec d → E →L[ℝ] F
  grad : Vec d → Fin d → E →L[ℝ] F
  memLp_top : MemLp toFun ⊤ (normalizedCubeMeasure Q)
  gradMemLp_top : ∀ i, MemLp (fun x => grad x i) ⊤ (normalizedCubeMeasure Q)
  hasWeakGradient : ∀ e : E, ∀ v : F, HasWeakGradientOn (openCubeSet Q)
    (fun x => inner ℝ v (toFun x e)) (fun x i => inner ℝ v (grad x i e))

 theorem hilbert_memLp_open_of_normalized {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (Q : TriadicCube d) {u : Vec d → E} (hu : MemLp u 2 (normalizedCubeMeasure Q)) :
    MemLp u 2 (volume.restrict (openCubeSet Q)) := by
  rw [← volume_restrict_cubeSet_eq_volume_restrict_openCubeSet]
  have h : volume.restrict (cubeSet Q) ≤ ENNReal.ofReal (cubeVolume Q) • normalizedCubeMeasure Q := by
    rw [normalizedCubeMeasure, cubeMeasure, smul_smul]
    have hc : ENNReal.ofReal (cubeVolume Q)*ENNReal.ofReal (cubeVolume Q)⁻¹ = 1 := by
      rw [← ENNReal.ofReal_mul (cubeVolume_nonneg Q), mul_inv_cancel₀ (cubeVolume_pos Q).ne', ENNReal.ofReal_one]
    rw [hc, one_smul]
  exact hu.of_measure_le_smul ENNReal.ofReal_ne_top h

/-- Applying a genuine operator Sobolev field to a fixed vector gives a genuine H1 field. -/
def HilbertOperatorW1Infinity.apply {d : ℕ} {Q : TriadicCube d} {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (b : HilbertOperatorW1Infinity Q E F) (e : E) : HilbertH1Function (openCubeSet Q) F where
  toFun x := b.toFun x e
  grad x i := b.grad x i e
  memL2 := hilbert_memLp_open_of_normalized Q
    (((ContinuousLinearMap.apply ℝ F e).comp_memLp' b.memLp_top).mono_exponent (by simp))
  gradMemL2 i := hilbert_memLp_open_of_normalized Q
    (((ContinuousLinearMap.apply ℝ F e).comp_memLp' (b.gradMemLp_top i)).mono_exponent (by simp))
  hasWeakGradient := b.hasWeakGradient e

 theorem HilbertOperatorW1Infinity.product_memLp {d : ℕ} {Q : TriadicCube d} {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (b : HilbertOperatorW1Infinity Q E F) {f : Vec d → E} (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    MemLp (fun x => b.toFun x (f x)) 2 (normalizedCubeMeasure Q) :=
  (ContinuousLinearMap.id ℝ (E →L[ℝ] F)).memLp_of_bilin 2 b.memLp_top hf

/-- A pointwise operator bound controls actual normalized product energy. -/
theorem hilbert_operator_product_energy_le {d : ℕ} {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Q : TriadicCube d) {b : Vec d → E →L[ℝ] F} {f : Vec d → E} {B : ℝ}
    (_hB : 0 ≤ B) (hb : ∀ᵐ x ∂normalizedCubeMeasure Q, ‖b x‖ ≤ B)
    (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hbf : MemLp (fun x => b x (f x)) 2 (normalizedCubeMeasure Q)) :
    hilbertEnergy Q (fun x => b x (f x)) ≤ B^2*hilbertEnergy Q f := by
  rw [hilbertEnergy, hilbertEnergy, ← integral_const_mul]
  apply integral_mono_ae (hbf.integrable_norm_pow (by norm_num)) ((hf.integrable_norm_pow (by norm_num)).const_mul _)
  filter_upwards [hb] with x hx
  have hn : ‖b x (f x)‖ ≤ B*‖f x‖ := (b x).le_opNorm (f x) |>.trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hn 2

end
end ASDExplicitGamma.Triadic
