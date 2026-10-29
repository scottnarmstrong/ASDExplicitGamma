module

public import ASDExplicitGamma.Triadic.DiagSobolev
public import Homogenization.Sobolev.Truncation.WeakGradientLimit

/-! Integration by parts against H¹ tests for the source H¹₀ residual. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization MeasureTheory Filter
open scoped Topology

noncomputable section

/-- The boundary-free weak integration-by-parts identity used by the
DIAG two-cell tent test. Only the potential has zero trace. -/
theorem diagH10_integrationByParts (Q : TriadicCube 2)
    (u : H10Function (openCubeSet Q)) (w : H1Function (openCubeSet Q)) (i : Fin 2) :
    (∫ x in openCubeSet Q, u.toH1Function.grad x i * w.toFun x) =
      -∫ x in openCubeSet Q, u.toH1Function.toFun x * w.grad x i := by
  let F (n : ℕ) := H1Function.ofContDiff (isOpen_openCubeSet Q)
    ((u.approx_smooth n).of_le (by simp)) (u.approx_hasCompactSupport n)
  have hv (n : ℕ) : (F n).toFun = u.approx n := rfl
  have hg (n : ℕ) : (F n).grad = fun x i => (fderiv ℝ (u.approx n) x) (basisVec i) := rfl
  have hmem (n : ℕ) : MemLp (u.approx n) 2 (volume.restrict (openCubeSet Q)) :=
    hv n ▸ (F n).memL2
  have hDmem (n : ℕ) : MemLp
      (fun x => (fderiv ℝ (u.approx n) x) (basisVec i)) 2 (volume.restrict (openCubeSet Q)) := by
    simpa only [hg] using (F n).gradMemL2 i
  have hl := tendsto_setIntegral_mul_of_tendsto_eLpNorm_two w.memL2 hDmem
    (u.toH1Function.gradMemL2 i) (u.tendsto_approx_grad i)
  have hr := tendsto_setIntegral_mul_of_tendsto_eLpNorm_two (w.gradMemL2 i) hmem
    u.toH1Function.memL2 u.tendsto_approx
  have heq (n : ℕ) :
      (∫ x in openCubeSet Q, (fderiv ℝ (u.approx n) x) (basisVec i) * w.toFun x) =
      -∫ x in openCubeSet Q, u.approx n x * w.grad x i := by
    simpa only [mul_comm] using w.hasWeakGradient i (u.approx n)
      (u.approx_smooth n) (u.approx_hasCompactSupport n) (u.approx_support_subset n)
  apply tendsto_nhds_unique hl
  apply hr.neg.congr'
  exact Filter.Eventually.of_forall fun n => (heq n).symm

end

end ASDExplicitGamma.Triadic
