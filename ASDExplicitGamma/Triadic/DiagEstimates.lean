module

public import ASDExplicitGamma.Triadic.DiagAffineEnergy
public import ASDExplicitGamma.Triadic.DiagResidualBounds

/-! The three sharp source DIAG interpolant estimates for all affine-data potentials. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization MeasureTheory
open scoped BigOperators

noncomputable section

local instance diagEstimatesFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- The H10 correction contributes no more weak energy than its affine-data potential. -/
theorem diagTiledWeakEnergy_correction_le (Q : TriadicCube 2) (j : ℕ) (p : Vec 2)
    (u : H10Function (openCubeSet Q)) :
    ASDExplicitGamma.Variational.lemmaVTiledWeakEnergy Q j u.toH1Function.grad ≤
      ASDExplicitGamma.Variational.lemmaVTiledWeakEnergy Q j
        (ASDExplicitGamma.Variational.lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u).grad := by
  rw [diagTiledWeakEnergy_affinePotential]
  exact le_add_of_nonneg_left (Finset.sum_nonneg fun i _ => sq_nonneg (p i))

/-- Squared sharp gradient estimate, including the affine load exactly. -/
theorem diagInterpolant_gradient_energy_le (Q : TriadicCube 2) (j : ℕ) (p : Vec 2)
    (u : H10Function (openCubeSet Q)) :
    let v := ASDExplicitGamma.Variational.lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
    ASDExplicitGamma.Variational.lemmaVTiledPositiveEnergy Q j (diagInterpolant Q j v).grad ≤
      ASDExplicitGamma.Variational.lemmaVTiledWeakEnergy Q j v.grad := by
  intro v
  rw [diagTiledPositiveEnergy_affineInterpolant, diagTiledWeakEnergy_affinePotential]
  exact add_le_add (le_refl (∑ i, p i^2)) (diagInterpolant_h10_gradient_energy_le Q j u)

/-- Squared sharp positive residual estimate for the actual source affine-data interpolant. -/
theorem diagInterpolant_residual_positive_energy_le (Q : TriadicCube 2) (j : ℕ) (p : Vec 2)
    (u : H10Function (openCubeSet Q)) :
    let v := ASDExplicitGamma.Variational.lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
    diagTiledScalarPositiveEnergy Q j (v-diagInterpolant Q j v).toFun ≤
      diagMeshRadius Q j^2*(2/Real.pi+1/2)^2*
        ASDExplicitGamma.Variational.lemmaVTiledWeakEnergy Q j v.grad := by
  intro v
  rw [diagInterpolant_affinePotential_residual]
  apply (diagInterpolant_h10_residual_positive_energy_le Q j u).trans
  exact mul_le_mul_of_nonneg_left (diagTiledWeakEnergy_correction_le Q j p u) (by positivity)

/-- Squared sharp L2 residual estimate, using the mean-zero Neumann constant. -/
theorem diagInterpolant_residual_L2_energy_le (Q : TriadicCube 2) (j : ℕ) (p : Vec 2)
    (u : H10Function (openCubeSet Q)) :
    let v := ASDExplicitGamma.Variational.lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
    energy Q (v-diagInterpolant Q j v).toFun ≤
      diagMeshRadius Q j^2*(planarC0+1/2)^2*
        ASDExplicitGamma.Variational.lemmaVTiledWeakEnergy Q j v.grad := by
  intro v
  rw [diagInterpolant_affinePotential_residual]
  apply (diagInterpolant_h10_residual_L2_energy_le Q j u).trans
  exact mul_le_mul_of_nonneg_left (diagTiledWeakEnergy_correction_le Q j p u) (by positivity)

theorem diagSqrt_energy_bound {E W C : ℝ} (hW : 0 ≤ W) (hC : 0 ≤ C) (h : E ≤ C^2*W) :
    Real.sqrt E ≤ C*Real.sqrt W := by
  apply (Real.sqrt_le_iff).2
  constructor
  · exact mul_nonneg hC (Real.sqrt_nonneg W)
  · simpa only [mul_pow, Real.sq_sqrt hW] using h

/-- Source P_br(grad Iv) ≤ W(v), with the sharp weak-face constant one. -/
theorem diagInterpolant_gradient_estimate (Q : TriadicCube 2) (j : ℕ) (p : Vec 2)
    (u : H10Function (openCubeSet Q)) :
    let v := ASDExplicitGamma.Variational.lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
    Real.sqrt (ASDExplicitGamma.Variational.lemmaVTiledPositiveEnergy Q j (diagInterpolant Q j v).grad) ≤
      Real.sqrt (ASDExplicitGamma.Variational.lemmaVTiledWeakEnergy Q j v.grad) := by
  intro v
  exact Real.sqrt_le_sqrt (diagInterpolant_gradient_energy_le Q j p u)

/-- Source P_br(v-Iv) ≤ r(2/pi+1/2)W(v). -/
theorem diagInterpolant_residual_positive_estimate (Q : TriadicCube 2) (j : ℕ) (p : Vec 2)
    (u : H10Function (openCubeSet Q)) :
    let v := ASDExplicitGamma.Variational.lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
    Real.sqrt (diagTiledScalarPositiveEnergy Q j (v-diagInterpolant Q j v).toFun) ≤
      diagMeshRadius Q j*(2/Real.pi+1/2)*
        Real.sqrt (ASDExplicitGamma.Variational.lemmaVTiledWeakEnergy Q j v.grad) := by
  intro v
  apply diagSqrt_energy_bound (ASDExplicitGamma.Variational.lemmaVTiledWeakEnergy_nonneg Q j v.grad)
    (mul_nonneg (diagMeshRadius_pos Q j).le (by positivity))
  simpa only [mul_pow, mul_assoc] using diagInterpolant_residual_positive_energy_le Q j p u

/-- Source normalized L2 error ≤ r(c0+1/2)W(v). -/
theorem diagInterpolant_residual_L2_estimate (Q : TriadicCube 2) (j : ℕ) (p : Vec 2)
    (u : H10Function (openCubeSet Q)) :
    let v := ASDExplicitGamma.Variational.lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
    Real.sqrt (energy Q (v-diagInterpolant Q j v).toFun) ≤
      diagMeshRadius Q j*(planarC0+1/2)*
        Real.sqrt (ASDExplicitGamma.Variational.lemmaVTiledWeakEnergy Q j v.grad) := by
  intro v
  apply diagSqrt_energy_bound (ASDExplicitGamma.Variational.lemmaVTiledWeakEnergy_nonneg Q j v.grad)
    (mul_nonneg (diagMeshRadius_pos Q j).le (add_nonneg diagPlanarC0_pos.le (by norm_num)))
  simpa only [mul_pow, mul_assoc] using diagInterpolant_residual_L2_energy_le Q j p u

/-- Actual affine-data tile gradients have convergent positive Haar series. -/
theorem diagInterpolant_cell_gradient_summable (Q : TriadicCube 2) (j : ℕ) (p : Vec 2)
    (u : H10Function (openCubeSet Q)) (k : Fin 2 → Fin (3^j)) (i : Fin 2) :
    let v := ASDExplicitGamma.Variational.lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
    Summable (fun n => (Real.sqrt 3)^(n+1)*energy (diagMeshCell Q j k)
      (cubeIncrement (diagMeshCell Q j k) (n+1) (fun x => (diagInterpolant Q j v).grad x i))) := by
  intro v
  have heq : (fun x => (diagInterpolant Q j v).grad x i) =
      fun x => (diagInterpolant Q j u.toH1Function).grad x i-(-p i) := by
    rw [diagInterpolant_affinePotential]
    funext x
    change p i+(diagInterpolant Q j u.toH1Function).grad x i =
      (diagInterpolant Q j u.toH1Function).grad x i-(-p i)
    ring
  rw [heq]
  have hf := memLp_on_descendant_of_memLp (diagMeshCell_mem Q j k)
    ((diagInterpolant Q j u.toH1Function).grad_memL2_normalizedCubeMeasure i)
  simp_rw [diagIncrement_succ_sub_const _ _ hf]
  exact diagInterpolant_h10_cell_gradient_summable Q j u k i

/-- Positive-series convergence on every actual descendant, in the H2 carrier. -/
theorem diagInterpolant_gradient_summable (Q : TriadicCube 2) (j : ℕ) (p : Vec 2)
    (u : H10Function (openCubeSet Q)) (R : TriadicCube 2) (hR : R ∈ descendantsAtDepth Q j) (i : Fin 2) :
    let v := ASDExplicitGamma.Variational.lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p u
    Summable (fun n => (Real.sqrt 3)^(n+1)*energy R
      (cubeIncrement R (n+1) (fun x => (diagInterpolant Q j v).grad x i))) := by
  let k := (diagMeshCellEquiv Q j).symm ⟨R,hR⟩
  have hcell : diagMeshCell Q j k = R := congrArg Subtype.val
    ((diagMeshCellEquiv Q j).apply_symm_apply ⟨R,hR⟩)
  rw [← hcell]
  exact diagInterpolant_cell_gradient_summable Q j p u k i

end

end ASDExplicitGamma.Triadic
