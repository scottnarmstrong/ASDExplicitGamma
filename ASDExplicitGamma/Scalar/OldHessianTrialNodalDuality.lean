module

public import ASDExplicitGamma.Scalar.OldHessianTrialPrincipalBudget
public import ASDExplicitGamma.Native.OldSignedQ3SourceAdmissibility
public import ASDExplicitGamma.Triadic.VectorHaarSymmetry

/-! Constant-one broken duality and its sharp one-half energy payment for
the actual nodal interpolation, before the signed covariance contraction. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- Arithmetic half-payment on nonnegative energies. -/
theorem old_hessian_sqrt_product_half {a b : ℝ} (ha : 0≤a) (hb : 0≤b) :
    Real.sqrt a*Real.sqrt b≤(a+b)/2 := by
  nlinarith only [sq_nonneg (Real.sqrt a-Real.sqrt b),Real.sq_sqrt ha,Real.sq_sqrt hb]

/-- Complete positivity of the actual zero-trace nodal gradient. -/
theorem old_hessian_nodal_gradient_positive (Q : TriadicCube 2) (fine : ℕ)
    (u : H10Function (openCubeSet Q)) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth Q fine) (i : Fin 2) :
    Summable (fun j => (Real.sqrt 3)^(j+1)*energy U
      (cubeIncrement U (j+1) (fun x => (diagInterpolant Q fine u.toH1Function).grad x i))) := by
  have hh := diagInterpolant_gradient_summable Q fine 0 u U hU i
  dsimp only at hh
  rw [old_signed_zero_affine_potential] at hh
  exact hh

/-- Nodal positive/weak duality pays the arithmetic half of the two genuine
weak energies. Positive-series convergence is supplied by the interpolant. -/
theorem old_hessian_nodal_duality_half (Q : TriadicCube 2) (fine : ℕ)
    (u : H10Function (openCubeSet Q)) (G : Vec 2 → Vec 2)
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q)) :
    |cubeAverage Q (fun x => vecDot (G x) ((diagInterpolant Q fine u.toH1Function).grad x))| ≤
      (lemmaVTiledWeakEnergy Q fine G+lemmaVTiledWeakEnergy Q fine u.toH1Function.grad)/2 := by
  have hpos := old_hessian_nodal_gradient_positive Q fine u
  have hp := lemmaV_tiled_pairing_le Q fine hG
    (diagInterpolant Q fine u.toH1Function).grad_memL2_normalizedCubeMeasure hpos
  have hw := lemmaVTiledWeakEnergy_nonneg Q fine G
  have hi := lemmaVTiledPositiveEnergy_nonneg Q fine (diagInterpolant Q fine u.toH1Function).grad
  have hy := old_hessian_sqrt_product_half hw hi
  have hsum : lemmaVTiledWeakEnergy Q fine G+
      lemmaVTiledPositiveEnergy Q fine (diagInterpolant Q fine u.toH1Function).grad ≤
        lemmaVTiledWeakEnergy Q fine G+lemmaVTiledWeakEnergy Q fine u.toH1Function.grad :=
    add_le_add (le_refl (lemmaVTiledWeakEnergy Q fine G)) (diagInterpolant_h10_gradient_energy_le Q fine u)
  have hdiv := div_le_div_of_nonneg_right hsum (by norm_num : (0:ℝ)≤2)
  exact hp.trans (hy.trans hdiv)

/-- A complete finite load family retains the same half coefficient. -/
theorem old_hessian_nodal_family_duality_half {A : Type*} [Fintype A]
    (Q : TriadicCube 2) (fine : ℕ) (u : A → H10Function (openCubeSet Q))
    (G : A → Vec 2 → Vec 2)
    (hG : ∀ a i, MemLp (fun x => G a x i) 2 (normalizedCubeMeasure Q)) :
    |∑ a : A,cubeAverage Q (fun x => vecDot (G a x) ((diagInterpolant Q fine (u a).toH1Function).grad x))| ≤
      ((∑ a : A,lemmaVTiledWeakEnergy Q fine (G a))+
        ∑ a : A,lemmaVTiledWeakEnergy Q fine (u a).toH1Function.grad)/2 := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun a _ =>
    old_hessian_nodal_duality_half Q fine (u a) (G a) (hG a))
  rw [←Finset.sum_div,Finset.sum_add_distrib] at hh
  exact hh

/-- A planar rotation leaves the entire weak energy unchanged. -/
theorem old_hessian_weak_energy_quarter_turn (Q : TriadicCube 2) (F : Vec 2 → Vec 2) :
    vectorWeakHaarEnergy Q (fun x => planarQuarterTurn (F x))=vectorWeakHaarEnergy Q F := by
  simp only [vectorWeakHaarEnergy,dualEnergy,Fin.sum_univ_two,planarQuarterTurn,
    ite_true,show (1:Fin 2)≠0 by decide,ite_false,primalEnergy_neg]
  ring

end
end ASDExplicitGamma.Scalar
