module

public import ASDExplicitGamma.Inverse.FullResponseIdentityReferenceCell
public import ASDExplicitGamma.Inverse.FullResponseShearedTracePositivity

/-! The complete identity trace is paid by deterministic exact-shear layers. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Variational
open scoped ENNReal

noncomputable section

/-- Literal normalized trace of the physically sheared clipped old response. -/
def fullResponseShearedCellTrace (M : ABKModel 2) (P : TriadicCube 2)
    (J : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  let R := assemblyPhysicalShearMatrix M (P.scale+40) P.scale J
    (((P.index 0:ℝ)-1/2)*(3:ℝ)^P.scale)
    (((P.index 1:ℝ)-1/2)*(3:ℝ)^P.scale) weights ω
  Matrix.trace (R.transpose*clippedCellMatrix M (P.scale+40) P (rootTau .full) ω*R)/4

/-- Positivity removes an arbitrary identity mask before the complete
physical-volume layer sum is taken. No random mask is conditioned on. -/
theorem full_response_identity_sheared_sum_le_layers
    (M : ABKModel 2) (Q : TriadicCube 2) (H : ℕ) (S : Set (TriadicCube 2))
    (J : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2)
    (w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) :
    (∑' i : HybridIdentityCell Q H S, ENNReal.ofReal
      (w i.val.1*(volume (cubeSet i.val.2.val)).toReal/(volume (cubeSet Q)).toReal *
        fullResponseShearedCellTrace M i.val.2.val J weights ω)) ≤
      ∑' n : ℕ, ENNReal.ofReal (w n*fullResponseShearedLayerTrace M Q H n J weights ω) := by
  classical
  let f : WhitneyIndexedCell Q H → ℝ≥0∞ := fun i => ENNReal.ofReal
    (w i.1*(volume (cubeSet i.2.val)).toReal/(volume (cubeSet Q)).toReal *
      fullResponseShearedCellTrace M i.2.val J weights ω)
  have hcomp := ENNReal.tsum_comp_le_tsum_of_injective
    (Subtype.val_injective : Function.Injective
      (fun i : HybridIdentityCell Q H S => i.val)) f
  apply hcomp.trans_eq
  change (∑' i : Σ n : ℕ, ↥(whitneyRootLayer Q H n), f i) = _
  rw [ENNReal.tsum_sigma']
  apply tsum_congr
  intro n
  rw [tsum_fintype]
  have hsum := Finset.sum_coe_sort (whitneyRootLayer Q H n)
    (fun P : TriadicCube 2 => ENNReal.ofReal
      (w n*(volume (cubeSet P)).toReal/(volume (cubeSet Q)).toReal *
        fullResponseShearedCellTrace M P J weights ω))
  change (∑ P : ↥(whitneyRootLayer Q H n), ENNReal.ofReal
    (w n*(volume (cubeSet P.val)).toReal/(volume (cubeSet Q)).toReal *
      fullResponseShearedCellTrace M P.val J weights ω)) = _
  rw [hsum]
  have hnonneg (P : TriadicCube 2) (hP : P ∈ whitneyRootLayer Q H n) :
      0 ≤ w n*(volume (cubeSet P)).toReal/(volume (cubeSet Q)).toReal *
        fullResponseShearedCellTrace M P J weights ω :=
    mul_nonneg
      (div_nonneg (mul_nonneg (hw n) ENNReal.toReal_nonneg) ENNReal.toReal_nonneg)
      (clipped_congruence_normalized_trace_nonneg M (P.scale+40) P
        (rootTau .full) ω _)
  rw [← ENNReal.ofReal_sum_of_nonneg hnonneg]
  congr 1
  rw [fullResponseShearedLayerTrace, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  dsimp only [fullResponseShearedCellTrace]
  ring

/-- The actual complete identity contribution in the root reference frame
is paid by the exact sheared clipped layers, including all later waves. -/
theorem full_response_identity_reference_sum_le_layers
    (M : ABKModel 2) (Q : TriadicCube 2) (H : ℕ) (hH : 377 ≤ H)
    (ω : Cutoff.CutoffSample 2) (J : ℤ) (hJ : Q.scale-1 ≤ J) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc (Q.scale-342) J, 0 ≤ weights k ∧ weights k ≤ 1) :
    let S := rootBadWhitneyCells M Q H (rootTau .full) (waveGateEta .full) ω
    (∑' i : HybridIdentityCell Q H S, ENNReal.ofReal
      (((volume (cubeSet i.val.2.val)).toReal/(volume (cubeSet Q)).toReal) *
        (Matrix.trace (toFullBlockMat (frameMatrix (Annealed.sigmaBar M (Q.scale-1) : ℝ)
          (coarseBlockMatrix (cubeSet i.val.2.val)
            (attenuatedCoefficient M (Q.scale-342) J weights ω))))/4))) ≤
      ENNReal.ofReal (rootEdelta .full) * ∑' n : ℕ, ENNReal.ofReal
        (rootAssemblyClock M.gamma H n*fullResponseShearedLayerTrace M Q H n J
          (sourceBandWeights (Q.scale-342) weights) ω) := by
  classical
  dsimp only
  let S := rootBadWhitneyCells M Q H (rootTau .full) (waveGateEta .full) ω
  let a := sourceBandWeights (Q.scale-342) weights
  let f : HybridIdentityCell Q H S → ℝ≥0∞ := fun i => ENNReal.ofReal
    (rootAssemblyClock M.gamma H i.val.1*(volume (cubeSet i.val.2.val)).toReal /
      (volume (cubeSet Q)).toReal*fullResponseShearedCellTrace M i.val.2.val J a ω)
  have hE : 0 ≤ rootEdelta .full := (Real.exp_pos _).le
  have hclock (n : ℕ) : 0 ≤ rootAssemblyClock M.gamma H n :=
    (root_assembly_clock_pos _ _ _).le
  have hterm (i : HybridIdentityCell Q H S) : ENNReal.ofReal
      (((volume (cubeSet i.val.2.val)).toReal/(volume (cubeSet Q)).toReal) *
        (Matrix.trace (toFullBlockMat (frameMatrix (Annealed.sigmaBar M (Q.scale-1) : ℝ)
          (coarseBlockMatrix (cubeSet i.val.2.val)
            (attenuatedCoefficient M (Q.scale-342) J weights ω))))/4)) ≤
        ENNReal.ofReal (rootEdelta .full)*f i := by
    let v := (volume (cubeSet i.val.2.val)).toReal/(volume (cubeSet Q)).toReal
    have hv : 0 ≤ v := div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    have hh := full_response_identity_reference_cell_le M Q H hH ω J hJ weights hw i
    rw [ENNReal.ofReal_mul hv]
    apply (mul_le_mul_of_nonneg_left hh (show 0 ≤ ENNReal.ofReal v from bot_le)).trans_eq
    have hreal : rootAssemblyClock M.gamma H i.val.1*
        (volume (cubeSet i.val.2.val)).toReal/(volume (cubeSet Q)).toReal *
          fullResponseShearedCellTrace M i.val.2.val J a ω =
      rootAssemblyClock M.gamma H i.val.1*(v*fullResponseShearedCellTrace M i.val.2.val J a ω) := by
      dsimp only [v]
      ring
    dsimp only [f]
    rw [hreal, ENNReal.ofReal_mul hE, ENNReal.ofReal_mul (hclock _), ENNReal.ofReal_mul hv]
    dsimp only [fullResponseShearedCellTrace, a]
    ac_rfl
  apply (ENNReal.tsum_le_tsum hterm).trans
  rw [ENNReal.tsum_mul_left]
  apply mul_le_mul_of_nonneg_left _ bot_le
  exact full_response_identity_sheared_sum_le_layers M Q H S J a ω
    (rootAssemblyClock M.gamma H) hclock

end
end ASDExplicitGamma.Inverse
