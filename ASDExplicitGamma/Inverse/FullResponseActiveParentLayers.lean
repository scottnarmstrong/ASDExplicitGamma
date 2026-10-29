module

public import ASDExplicitGamma.Inverse.FullResponseActiveLayerSum

/-! Exact regrouping of indexed active parents into complete spatial layers. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
open scoped ENNReal
noncomputable section

/-- The all-parent density charge is exactly the complete deterministic layer
sum. This reuses the sigma-index grouping pattern without changing the
full-row sharp c0/c1 coefficient or any parent volume. -/
theorem full_response_active_parent_sum_eq_layers
    (M : ABKModel 2) (Q : TriadicCube 2) (H : ℕ) (N : ℤ)
    (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) :
    (∑' P : WhitneyIndexedCell Q H, ENNReal.ofReal
      (fullResponseReferenceParentCoefficient M Q H N weights ω P*
        (planarGradientCharge 40+1)*
          (∑ e : Fin 3, ∫ x in cubeSet P.2.val,
            (layerResolutionDiameter M Q H (rootTau .full) (waveGateEta .full)
              P.1 e ω x)^2)/(volume (cubeSet Q)).toReal)) =
      ENNReal.ofReal (rootEdelta .full*(planarGradientCharge 40+1))*
        ∑' n : ℕ, ENNReal.ofReal (rootAssemblyClock M.gamma H n*
          fullResponseActiveLayerDensity M Q H n N weights ω) := by
  classical
  let F := fun n : ℕ => fun U : TriadicCube 2 =>
    ((volume (cubeSet U)).toReal/(volume (cubeSet Q)).toReal)*
      (fullResponseTraceC0+fullResponseTraceC1*
        (fullResponseParentWaveMean M U (Q.scale-342) N weights ω)^2)*
      ∑ e : Fin 3, cubeAverage U (fun x =>
        (layerResolutionDiameter M Q H (rootTau .full) (waveGateEta .full) n e ω x)^2)
  have hC : 0 ≤ rootEdelta .full*(planarGradientCharge 40+1) := by
    unfold rootEdelta planarGradientCharge
    positivity
  change (∑' P : Σ n : ℕ, ↥(whitneyRootLayer Q H n), _) = _
  rw [ENNReal.tsum_sigma',← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro n
  rw [tsum_fintype]
  have hlocal (U : ↥(whitneyRootLayer Q H n)) :
      ENNReal.ofReal
        (fullResponseReferenceParentCoefficient M Q H N weights ω ⟨n,U⟩*
          (planarGradientCharge 40+1)*
          (∑ e : Fin 3, ∫ x in cubeSet U.val,
            (layerResolutionDiameter M Q H (rootTau .full) (waveGateEta .full) n e ω x)^2)/
              (volume (cubeSet Q)).toReal) =
        ENNReal.ofReal (rootEdelta .full*(planarGradientCharge 40+1))*
          ENNReal.ofReal (rootAssemblyClock M.gamma H n*F n U.val) := by
    rw [← ENNReal.ofReal_mul hC]
    congr 1
    dsimp only [fullResponseReferenceParentCoefficient,F]
    simp_rw [cubeAverage,← Finset.mul_sum]
    rw [volume_cubeSet_toReal,volume_cubeSet_toReal]
    field_simp [(cubeVolume_pos U.val).ne',(cubeVolume_pos Q).ne']
  simp_rw [hlocal]
  rw [← Finset.mul_sum]
  congr 1
  have hF (U : TriadicCube 2) : 0 ≤ F n U := by
    have hc0 : 0 ≤ fullResponseTraceC0 := by unfold fullResponseTraceC0 rootTau; positivity
    have hc1 : 0 ≤ fullResponseTraceC1 := by unfold fullResponseTraceC1 rootTau; positivity
    dsimp only [F]
    apply mul_nonneg
    · exact mul_nonneg (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
        (add_nonneg hc0 (mul_nonneg hc1 (sq_nonneg _)))
    · apply Finset.sum_nonneg
      intro e _
      unfold cubeAverage
      exact mul_nonneg (inv_nonneg.mpr (cubeVolume_pos U).le)
        (integral_nonneg (fun _ => sq_nonneg _))
  rw [← ENNReal.ofReal_sum_of_nonneg (fun U _ =>
    mul_nonneg (root_assembly_clock_pos _ _ _).le (hF U.val))]
  congr 1
  rw [← Finset.mul_sum,Finset.sum_coe_sort]
  congr 1
  dsimp only [fullResponseActiveLayerDensity,F]
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

end
end ASDExplicitGamma.Inverse
