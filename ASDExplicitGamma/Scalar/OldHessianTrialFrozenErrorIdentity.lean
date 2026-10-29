module

public import ASDExplicitGamma.Scalar.OldHessianTrialMinusKernelDecomposition

/-! Exact deterministic covariance error: actual parent harmonic boundary
covariance minus the joint fine-cell centered covariance. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main
noncomputable section

/-- The physical white section has exactly one shell variance on each cell. -/
theorem old_hessian_white_section_energy (U : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0<l}) :
    hilbertEnergy U (q3Section b L h3Zero)=b^2 := by
  simp only [hilbertEnergy,old_signed_raw_white_norm_sq,integral_const,Measure.real_def,
    normalizedCubeMeasure_apply_univ,ENNReal.toReal_one,one_smul]

/-- Exact source equation (10), entrywise, before taking any absolute value:
the harmonic parent remainder and the centered fine covariance both remain. -/
theorem old_hessian_frozen_covariance_error_identity (Q : TriadicCube 2) (depth : ℕ)
    (b : ℝ) (L : {l : ℝ // 0<l}) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth Q depth) (i k : Fin 2) :
    let F := q3Section b L h3Zero
    let G := (oldHessianMinusKernel Q b L i k).toFun
    oldHessianMeanCovarianceError Q U b L k i=
      cubeAverage U (fun x => inner ℝ (F x) ((oldSignedRemainderKernel Q b L false (i,k)).toFun x))-
        cubeAverage U (fun x => inner ℝ (F x-hilbertCubeAverage U F) (G x-hilbertCubeAverage U G)) := by
  intro F G
  let g := (oldHessianMinusKernel Q b L i k).restrict
    (openCubeSet_subset_of_mem_descendantsAtDepth hU) (measurableSet_openCubeSet Q)
  let R := (oldSignedRemainderKernel Q b L false (i,k)).restrict
    (openCubeSet_subset_of_mem_descendantsAtDepth hU) (measurableSet_openCubeSet Q)
  have hF : MemLp F 2 (normalizedCubeMeasure U) := old_hessian_white_section_memLp U b L
  have hG : MemLp G 2 (normalizedCubeMeasure U) := g.memL2_normalized U
  have hR : MemLp R.toFun 2 (normalizedCubeMeasure U) := R.memL2_normalized U
  have hcent := old_hessian_hilbert_covariance_centering U F G hF hG
  have havg : cubeAverage U (fun x => inner ℝ (F x) (G x))=
      (b^2/2)*responsePlanarJ k i+
        cubeAverage U (fun x => inner ℝ (F x) (R.toFun x)) := by
    have he := integral_congr_ae (old_hessian_minus_point_covariance Q depth b L U hU i k)
    have hi := old_hessian_hilbert_pairing_integrable U F R.toFun hF hR
    change (∫ x,inner ℝ (F x) (G x) ∂normalizedCubeMeasure U)=
      ∫ x,(b^2/2)*responsePlanarJ k i+inner ℝ (F x) (R.toFun x) ∂normalizedCubeMeasure U at he
    rw [integral_add (integrable_const _) hi] at he
    simpa only [cubeAverage_eq_integral_normalizedCubeMeasure,integral_const,Measure.real_def,
      normalizedCubeMeasure_apply_univ,ENNReal.toReal_one,one_smul] using he
  have hRfun : R.toFun=(oldSignedRemainderKernel Q b L false (i,k)).toFun := rfl
  rw [hRfun] at havg
  change oldHessianMeanCovariance Q U b L k i-(b^2/2)*responsePlanarJ k i=_
  rw [old_hessian_mean_covariance_kernel Q depth b L U hU i k,hcent,havg]
  ring

/-- Constant-one entrywise boundary/oscillation bill for that exact error.
It is stated in actual kernel energies, before source numerical caps. -/
theorem old_hessian_frozen_covariance_error_entry_bound (Q : TriadicCube 2) (depth : ℕ)
    (b : ℝ) (L : {l : ℝ // 0<l}) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth Q depth) (i k : Fin 2) :
    let F := q3Section b L h3Zero
    let G := (oldHessianMinusKernel Q b L i k).toFun
    |oldHessianMeanCovarianceError Q U b L k i| ≤
      |b| * Real.sqrt (hilbertEnergy U (oldSignedRemainderKernel Q b L false (i,k)).toFun)+
        Real.sqrt (hilbertEnergy U (fun x => F x-hilbertCubeAverage U F))*
          Real.sqrt (hilbertEnergy U (fun x => G x-hilbertCubeAverage U G)) := by
  intro F G
  let g := (oldHessianMinusKernel Q b L i k).restrict
    (openCubeSet_subset_of_mem_descendantsAtDepth hU) (measurableSet_openCubeSet Q)
  let R := (oldSignedRemainderKernel Q b L false (i,k)).restrict
    (openCubeSet_subset_of_mem_descendantsAtDepth hU) (measurableSet_openCubeSet Q)
  have hF : MemLp F 2 (normalizedCubeMeasure U) := old_hessian_white_section_memLp U b L
  have hG : MemLp G 2 (normalizedCubeMeasure U) := g.memL2_normalized U
  have hR : MemLp R.toFun 2 (normalizedCubeMeasure U) := R.memL2_normalized U
  have hb := old_hessian_hilbert_pairing_cauchy U F R.toFun hF hR
  rw [old_hessian_white_section_energy,Real.sqrt_sq_eq_abs] at hb
  have hc := old_hessian_hilbert_pairing_cauchy U
    (fun x => F x-hilbertCubeAverage U F) (fun x => G x-hilbertCubeAverage U G)
    (hF.sub (memLp_const _)) (hG.sub (memLp_const _))
  rw [old_hessian_frozen_covariance_error_identity Q depth b L U hU i k]
  exact (abs_sub _ _).trans (add_le_add hb hc)

end
end ASDExplicitGamma.Scalar
