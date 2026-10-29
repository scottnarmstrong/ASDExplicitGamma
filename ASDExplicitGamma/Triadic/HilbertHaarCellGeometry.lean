module

public import ASDExplicitGamma.Triadic.HilbertHaarOrthogonal

/-! Bochner means, Sobolev restrictions, and normalized energy on actual tiles. -/

@[expose] public section
namespace ASDExplicitGamma.Triadic
open Homogenization MeasureTheory
open scoped BigOperators
noncomputable section

 theorem hilbert_ae_descendant {d : ℕ} {Q R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) {P : Vec d → Prop} (hP : ∀ᵐ x ∂normalizedCubeMeasure Q, P x) :
    ∀ᵐ x ∂normalizedCubeMeasure R, P x := by
  rw [normalizedCubeMeasure_descendant_eq_smul_restrict hR]
  exact Measure.ae_smul_measure (hP.filter_mono ae_restrict_le) _

 theorem hilbert_ae_cubeSet {d : ℕ} (Q : TriadicCube d) : ∀ᵐ x ∂normalizedCubeMeasure Q, x ∈ cubeSet Q := by
  unfold normalizedCubeMeasure cubeMeasure
  exact Measure.ae_smul_measure (ae_restrict_mem (measurableSet_cubeSet Q)) _

 theorem hilbertCubeAverage_congr_on {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Q : TriadicCube d) {u v : Vec d → E} (h : ∀ x ∈ cubeSet Q, u x=v x) :
    hilbertCubeAverage Q u = hilbertCubeAverage Q v :=
  hilbertCubeAverage_congr_ae Q ((hilbert_ae_cubeSet Q).mono fun x hx => h x hx)

 theorem hilbertEnergy_congr_on {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (Q : TriadicCube d) {u v : Vec d → E} (h : ∀ x ∈ cubeSet Q, u x=v x) : hilbertEnergy Q u = hilbertEnergy Q v :=
  hilbertEnergy_congr_ae Q ((hilbert_ae_cubeSet Q).mono fun x hx => h x hx)

 theorem hilbertCubeProjection_add {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (Q : TriadicCube d) (j : ℕ) {u v : Vec d → E}
    (hu : MemLp u 2 (normalizedCubeMeasure Q)) (hv : MemLp v 2 (normalizedCubeMeasure Q)) :
    hilbertCubeProjection Q j (fun x => u x+v x) = fun x => hilbertCubeProjection Q j u x+hilbertCubeProjection Q j v x := by
  classical
  funext x
  unfold hilbertCubeProjection
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro R hR
  split_ifs with hx
  · exact integral_add ((hilbert_memLp_descendant hR hu).integrable one_le_two)
      ((hilbert_memLp_descendant hR hv).integrable one_le_two)
  · exact (zero_add _).symm

 theorem hilbertEnergy_eq_descendantsAverage {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (Q : TriadicCube d) (j : ℕ) {f : Vec d → E} (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    hilbertEnergy Q f = descendantsAverage Q j (fun R => hilbertEnergy R f) := by
  rw [← hilbertEnergy_norm, energy_eq_descendantsAverage Q j hf.norm]
  simp only [hilbertEnergy_norm]

 theorem hilbertEnergy_const {d : ℕ} {E : Type*} [NormedAddCommGroup E] (Q : TriadicCube d) (c : E) :
    hilbertEnergy Q (fun _ => c) = ‖c‖^2 := by
  simp [hilbertEnergy, Measure.real_def, normalizedCubeMeasure_apply_univ]

 def HilbertH1Function.restrict {d : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {U V : Set (Vec d)} (u : HilbertH1Function V E) (hUV : U ⊆ V) (hV : MeasurableSet V) : HilbertH1Function U E where
  toFun := u.toFun
  grad := u.grad
  memL2 := u.memL2.mono_measure (Measure.restrict_mono hUV le_rfl)
  gradMemL2 i := (u.gradMemL2 i).mono_measure (Measure.restrict_mono hUV le_rfl)
  hasWeakGradient e := hasWeakGradientOn_mono hUV hV (u.hasWeakGradient e)

end
end ASDExplicitGamma.Triadic
