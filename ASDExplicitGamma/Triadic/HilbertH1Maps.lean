module

public import ASDExplicitGamma.Triadic.HilbertHaarCoordinates
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Bounded linear images of the genuine Hilbert H1 weak-derivative graph. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization MeasureTheory

noncomputable section

/-- Bounded linear maps preserve actual Hilbert-valued weak derivatives. -/
def HilbertH1Function.map {d : ℕ} {U : Set (Vec d)} {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (u : HilbertH1Function U E) (L : E →L[ℝ] F) : HilbertH1Function U F where
  toFun x := L (u.toFun x)
  grad x i := L (u.grad x i)
  memL2 := L.comp_memLp' u.memL2
  gradMemL2 i := L.comp_memLp' (u.gradMemL2 i)
  hasWeakGradient e := by
    have h := u.hasWeakGradient (L.adjoint e)
    simpa only [L.adjoint_inner_left] using h

/-- A contraction cannot increase the true normalized L2 energy. -/
theorem hilbertEnergy_map_le {d : ℕ} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (Q : TriadicCube d) (L : E →L[ℝ] F)
    (hL : ‖L‖ ≤ 1) {u : Vec d → E} (hu : MemLp u 2 (normalizedCubeMeasure Q)) :
    hilbertEnergy Q (fun x => L (u x)) ≤ hilbertEnergy Q u := by
  apply integral_mono_ae ((L.comp_memLp' hu).integrable_norm_pow (by norm_num))
    (hu.integrable_norm_pow (by norm_num))
  apply Filter.Eventually.of_forall
  intro x
  have hnorm : ‖L (u x)‖ ≤ ‖u x‖ := (L.le_opNorm (u x)).trans
    ((mul_le_mul_of_nonneg_right hL (norm_nonneg _)).trans_eq (one_mul _))
  exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2

/-- Actual field equivalence classes determine the normalized Hilbert energy. -/
theorem hilbertEnergy_congr_ae {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (Q : TriadicCube d) {u v : Vec d → E} (huv : u =ᵐ[normalizedCubeMeasure Q] v) :
    hilbertEnergy Q u = hilbertEnergy Q v := by
  apply integral_congr_ae
  filter_upwards [huv] with x hx
  rw [hx]

theorem hilbertCubeAverage_congr_ae {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (Q : TriadicCube d) {u v : Vec d → E}
    (huv : u =ᵐ[normalizedCubeMeasure Q] v) : hilbertCubeAverage Q u = hilbertCubeAverage Q v :=
  integral_congr_ae huv

end

end ASDExplicitGamma.Triadic
