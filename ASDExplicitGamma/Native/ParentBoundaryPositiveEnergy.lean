module

public import ASDExplicitGamma.Native.ParentBoundaryRowH1
public import ASDExplicitGamma.Triadic.HilbertPoincareConstants
public import ASDExplicitGamma.Triadic.PlanarConstants
public import ASDExplicitGamma.Triadic.TriadicProjection
public import ASDExplicitGamma.Triadic.VectorHaar
public import Homogenization.CoarseGraining.Subadditivity

/-! Sharp squared positive-Haar estimate for genuine scalar H1 functions,
including independent fine-cell restrictions. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Triadic
noncomputable section

private def scalarHilbertH1 {U : Set (Vec 2)} (u : H1Function U) : HilbertH1Function U ℝ where
  toFun := u.toFun
  grad := u.grad
  memL2 := u.memL2
  gradMemL2 := u.gradMemL2
  hasWeakGradient z := by
    have ht := (z • u).hasWeakGradient
    change HasWeakGradientOn U (fun x => z*u x) (fun x i => z*u.grad x i) at ht
    simpa only [Real.inner_apply] using ht

/-- The sharp squared positive-Haar estimate keeps the actual L2 energy
and pays planarC1 only on the actual spatial gradient energy. -/
theorem parent_boundary_scalar_positive_energy (Q : TriadicCube 2)
    (u : H1Function (openCubeSet Q)) :
    positiveHaarNorm Q u.toFun^2 ≤ energy Q u.toFun+
      cubeScaleFactor Q^2*planarC1^2*∑ i : Fin 2,energy Q (fun x => u.grad x i) := by
  have hq : 1<Real.sqrt 3 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ)≤3),Real.sqrt_nonneg (3:ℝ)]
  have hq9 : Real.sqrt 3<9 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0:ℝ)≤3),Real.sqrt_nonneg (3:ℝ)]
  have hp := (hilbert_positive_poincare_of_weight Q hq hq9 (scalarHilbertH1 u)).2.1
  have hc : haarPoincareM2 (Real.sqrt 3)=planarC1^2 := by
    rw [planarC1_sq]
    unfold haarPoincareM2
    rw [mul_comm (1-Real.sqrt 3/9)]
  rw [hc] at hp
  rw [positiveHaarNorm,Real.sq_sqrt (primalEnergy_nonneg Q _ (Real.sqrt_nonneg _) _)]
  simpa only [scalarHilbertH1,hilbertPrimalEnergy_real,hilbertEnergy_real,hilbertGradientEnergy] using hp

/-- The SAME parent H1 function restricted to a fine partition has the
sharp squared positive estimate at the fine scale, with exact parent energies. -/
theorem parent_boundary_broken_positive_energy (Q : TriadicCube 2) (depth : ℕ)
    (u : H1Function (openCubeSet Q)) :
    descendantsAverage Q depth (fun U => positiveHaarNorm U u.toFun^2) ≤
      energy Q u.toFun+(cubeScaleFactor Q/3^depth)^2*planarC1^2*
        ∑ i : Fin 2,energy Q (fun x => u.grad x i) := by
  have hlocal (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) :=
    parent_boundary_scalar_positive_energy U (u.restrictToOpenSubcube hU)
  have hscale (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) : cubeScaleFactor U=cubeScaleFactor Q/3^depth :=
    cubeScaleFactor_descendant_eq_div_pow hU
  have hlocal' (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) :
      positiveHaarNorm U u.toFun^2 ≤ energy U u.toFun+
        (cubeScaleFactor Q/3^depth)^2*planarC1^2*∑ i : Fin 2,energy U (fun x => u.grad x i) := by
    simpa only [H1Function.restrictToOpenSubcube_toFun,H1Function.restrictToOpenSubcube_grad,hscale U hU] using hlocal U hU
  have havg := descendantsAverage_le hlocal'
  rw [descendantsAverage_add,descendantsAverage_mul_left,Homogenization.descendantsAverage_sum,
    ←energy_eq_descendantsAverage Q depth u.memL2_normalizedCubeMeasure] at havg
  simp_rw [←energy_eq_descendantsAverage Q depth (u.grad_memL2_normalizedCubeMeasure _)] at havg
  exact havg

end
end ASDExplicitGamma.Native
