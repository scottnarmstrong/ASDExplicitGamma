module

public import ASDExplicitGamma.Native.OldSignedFiniteMinkowski
public import ASDExplicitGamma.Native.OldSignedRowProductBounds
public import ASDExplicitGamma.Main.FlatFieldH1Bounds
public import ASDExplicitGamma.Main.HilbertFiniteCoordinates

/-! Dimension-free weak-potential bounds for actual finite zero-trace
families, using the existing sharp Dirichlet bridges coordinatewise. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Triadic ASDExplicitGamma.Main
noncomputable section

/-- A genuine finite zero-trace potential family as a Hilbert H1 field. -/
def oldSignedDirichletFamily {I : Type*} [Fintype I] (Q : TriadicCube 2)
    (u : I → H10Function (openCubeSet Q)) :
    HilbertH1Function (openCubeSet Q) (EuclideanSpace ℝ I) :=
  mainHilbertH1OfCoordinates Q (fun i => (u i).toH1Function)

/-- Positive Haar weak-potential bound for a finite actual zero-trace
family, without losing a factor from the family size. -/
theorem old_signed_dirichlet_family_positive_bound {I : Type*} [Fintype I]
    (Q : TriadicCube 2) (u : I → H10Function (openCubeSet Q)) :
    hilbertPositiveHaarNorm Q (Real.sqrt 3) (oldSignedDirichletFamily Q u).toFun≤
      cubeScaleFactor Q*planarFD*Real.sqrt
        (∑ i,vectorWeakHaarNorm Q (fun x k => (u i).toH1Function.grad x k)^2) := by
  let F := oldSignedDirichletFamily Q u
  have hp := (old_signed_hilbert_h1_positive_bound Q F).1
  have hFD : 0≤cubeScaleFactor Q*planarFD :=
    mul_nonneg (Triadic.cubeScaleFactor_pos' Q).le (by unfold planarFD; positivity)
  have ht := old_signed_finite_sqrt_energy_bound
    (fun i => vectorWeakHaarNorm Q (fun x k => (u i).toH1Function.grad x k)^2)
    (fun _ : I => (0:ℝ)) (fun i => positiveHaarNorm Q (u i).toH1Function.toFun)
    hFD
    (show (0:ℝ)≤0 by norm_num) (fun _ => sq_nonneg _) (fun _ => le_rfl)
    (fun _ => Real.sqrt_nonneg _) (fun i => by
      rw [Real.sqrt_sq (show 0≤vectorWeakHaarNorm Q (fun x k => (u i).toH1Function.grad x k)
        from Real.sqrt_nonneg _)]
      simpa only [zero_mul,add_zero] using dirichlet_positiveHaar_bridge Q (u i))
  simp only [zero_mul,add_zero,positiveHaarNorm] at ht
  simp_rw [Real.sq_sqrt (primalEnergy_nonneg Q (Real.sqrt 3) (Real.sqrt_nonneg _) _)] at ht
  rw [hilbertPositiveHaarNorm,main_hilbertPrimalEnergy_euclidean Q (F.memL2_normalized Q) hp]
  exact ht

/-- The same family satisfies the L2 weak-potential bound on the identical
sum of actual weak gradient energies. -/
theorem old_signed_dirichlet_family_l2_bound {I : Type*} [Fintype I]
    (Q : TriadicCube 2) (u : I → H10Function (openCubeSet Q)) :
    hilbertL2Norm Q (oldSignedDirichletFamily Q u).toFun≤
      cubeScaleFactor Q*planarCD*Real.sqrt
        (∑ i,vectorWeakHaarNorm Q (fun x k => (u i).toH1Function.grad x k)^2) := by
  have hCD : 0≤cubeScaleFactor Q*planarCD :=
    mul_nonneg (Triadic.cubeScaleFactor_pos' Q).le (Real.sqrt_nonneg _)
  have ht := old_signed_finite_sqrt_energy_bound
    (fun i => vectorWeakHaarNorm Q (fun x k => (u i).toH1Function.grad x k)^2)
    (fun _ : I => (0:ℝ)) (fun i => Real.sqrt (energy Q (u i).toH1Function.toFun))
    hCD
    (show (0:ℝ)≤0 by norm_num) (fun _ => sq_nonneg _) (fun _ => le_rfl)
    (fun _ => Real.sqrt_nonneg _) (fun i => by
      rw [Real.sqrt_sq (show 0≤vectorWeakHaarNorm Q (fun x k => (u i).toH1Function.grad x k)
        from Real.sqrt_nonneg _)]
      simpa only [zero_mul,add_zero] using dirichlet_L2_bridge Q (u i))
  simp only [zero_mul,add_zero] at ht
  simp_rw [Real.sq_sqrt (energy_nonneg Q _)] at ht
  rw [hilbertL2Norm,main_hilbertEnergy_euclidean Q ((oldSignedDirichletFamily Q u).memL2_normalized Q)]
  exact ht

end
end ASDExplicitGamma.Native
