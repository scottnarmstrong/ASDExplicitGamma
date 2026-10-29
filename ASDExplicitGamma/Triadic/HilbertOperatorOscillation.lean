module

public import ASDExplicitGamma.Triadic.HilbertHaarCellGeometry

/-! Sharp cell oscillation of an operator Sobolev field acting on a vector mean. -/

@[expose] public section
namespace ASDExplicitGamma.Triadic
open Homogenization MeasureTheory
open scoped BigOperators
noncomputable section

 theorem hilbert_operator_gradient_energy_le {d : ℕ} {Q R : TriadicCube d} {j : ℕ} {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (b : HilbertOperatorW1Infinity Q E F) (hR : R ∈ descendantsAtDepth Q j) (e : E) {D : ℝ}
    (hD : ∀ᵐ x ∂normalizedCubeMeasure Q, (∑ i, ‖b.grad x i‖^2) ≤ D^2) :
    hilbertGradientEnergy R (fun x i => b.grad x i e) ≤ D^2*‖e‖^2 := by
  have hi (i : Fin d) : Integrable (fun x => ‖b.grad x i e‖^2) (normalizedCubeMeasure R) := by
    have h := (ContinuousLinearMap.apply ℝ F e).comp_memLp' ((b.gradMemLp_top i).mono_exponent (by simp : (2:ENNReal) ≤ ⊤))
    exact (hilbert_memLp_descendant hR h).integrable_norm_pow (by norm_num)
  have hpoint : ∀ᵐ x ∂normalizedCubeMeasure R, (∑ i, ‖b.grad x i e‖^2) ≤ D^2*‖e‖^2 := by
    filter_upwards [hilbert_ae_descendant hR hD] with x hx
    calc
      _ ≤ ∑ i, ‖b.grad x i‖^2*‖e‖^2 := Finset.sum_le_sum fun i _ => by
        simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) ((b.grad x i).le_opNorm e) 2
      _ = (∑ i, ‖b.grad x i‖^2)*‖e‖^2 := (Finset.sum_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hx (sq_nonneg _)
  unfold hilbertGradientEnergy hilbertEnergy
  rw [← integral_finsetSum Finset.univ (fun i _ => hi i)]
  have h := integral_mono_ae (integrable_finsetSum Finset.univ (fun i _ => hi i)) (integrable_const (D^2*‖e‖^2)) hpoint
  simpa only [integral_const, Measure.real_def, normalizedCubeMeasure_apply_univ, ENNReal.toReal_one, one_smul] using h

/-- Cellwise operator oscillation on a conditional mean has the exact 1/pi constant. -/
theorem hilbert_operator_mean_oscillation_energy_le {d : ℕ} {Q : TriadicCube d} {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (b : HilbertOperatorW1Infinity Q E F) (j : ℕ) {f : Vec d → E} (hf : MemLp f 2 (normalizedCubeMeasure Q)) {D : ℝ}
    (hD : ∀ᵐ x ∂normalizedCubeMeasure Q, (∑ i, ‖b.grad x i‖^2) ≤ D^2) :
    let v := fun x => b.toFun x (hilbertCubeProjection Q j f x)
    hilbertEnergy Q (fun x => v x-hilbertCubeProjection Q j v x) ≤
      cubeScaleFactor Q^2/(9^j*Real.pi^2)*D^2*hilbertEnergy Q f := by
  let v := fun x => b.toFun x (hilbertCubeProjection Q j f x)
  have hv : MemLp v 2 (normalizedCubeMeasure Q) := b.product_memLp (hilbertCubeProjection_memLp Q j f 2)
  change hilbertEnergy Q (fun x => v x-hilbertCubeProjection Q j v x) ≤ _
  rw [hilbertEnergy_eq_descendantsAverage Q j (f := fun x => v x-hilbertCubeProjection Q j v x) (hv.sub (hilbertCubeProjection_memLp Q j v 2))]
  have hcell (R : TriadicCube d) (hR : R ∈ descendantsAtDepth Q j) :
      hilbertEnergy R (fun x => v x-hilbertCubeProjection Q j v x) ≤
        cubeScaleFactor Q^2/(9^j*Real.pi^2)*D^2*hilbertEnergy R (hilbertCubeProjection Q j f) := by
    let e := hilbertCubeAverage R f
    let u := (b.apply e).restrict (openCubeSet_subset_of_mem_descendantsAtDepth hR)
      (by rw [openCubeSet_eq_box]; exact MeasurableSet.univ_pi fun _ => measurableSet_Ioo)
    have heval (x : Vec d) (hx : x ∈ cubeSet R) : v x=u.toFun x := by
      change b.toFun x (hilbertCubeProjection Q j f x) = b.toFun x e
      rw [hilbertCubeProjection_eq_average Q j f hR hx]
    have hmean : hilbertCubeAverage R v = hilbertCubeAverage R u.toFun := hilbertCubeAverage_congr_on R heval
    have heq : hilbertEnergy R (fun x => v x-hilbertCubeProjection Q j v x) =
        hilbertEnergy R (fun x => u.toFun x-hilbertCubeAverage R u.toFun) := by
      apply hilbertEnergy_congr_on
      intro x hx
      rw [hilbertCubeProjection_eq_average Q j v hR hx, heval x hx, hmean]
    have hproj : hilbertEnergy R (hilbertCubeProjection Q j f) = ‖e‖^2 := by
      rw [hilbertEnergy_congr_on R (fun x hx => hilbertCubeProjection_eq_average Q j f hR hx), hilbertEnergy_const]
    rw [heq, hproj]
    have hg := hilbert_operator_gradient_energy_le b hR e hD
    have hp := (hilbert_cube_poincare R u).trans (mul_le_mul_of_nonneg_left hg (sq_nonneg _))
    refine hp.trans_eq ?_
    rw [cubeScaleFactor_descendant_eq_div_pow hR, div_pow, div_pow]
    have h9 : ((3:ℝ)^j)^2 = (9:ℝ)^j := by rw [← pow_mul, Nat.mul_comm j 2, pow_mul]; norm_num
    rw [h9]
    ring
  have h := descendantsAverage_le hcell
  rw [descendantsAverage_mul_left,
    ← hilbertEnergy_eq_descendantsAverage Q j (hilbertCubeProjection_memLp Q j f 2)] at h
  exact h.trans (mul_le_mul_of_nonneg_left (hilbertEnergy_projection_le Q j hf)
    (mul_nonneg (div_nonneg (sq_nonneg _) (by positivity)) (sq_nonneg _)))

end
end ASDExplicitGamma.Triadic
