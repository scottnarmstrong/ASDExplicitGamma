module

public import ASDExplicitGamma.Inverse.StoppedKuhnGradientCharge
public import ASDExplicitGamma.Inverse.StoppedPlanarFluxAlgebra
public import ASDExplicitGamma.Inverse.StoppedH10RotatedGradient

/-! Source planar flux companion of the single actual midpoint map. Its
correction is an exact rotated H1_0 gradient, hence has zero divergence and
zero normal trace for every loading on the same map. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory ASDExplicitGamma.Triadic ASDExplicitGamma.Response
open Algsuperdiff.Section3 Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Whitney
noncomputable section

variable (M : ABKModel 2) (Q : TriadicCube 2) (H : ℕ) (hH : 333 ≤ H)
  (τ η : ℝ) (ω : Cutoff.CutoffSample 2)
  (hgood : ∀ k, H ≤ k → ω ∉ separationFailure
    (q3PlanarMarks M (Q.scale-k) τ η) k (rootBlockStart Q k))
  (S : Set (TriadicCube 2)) (hS : S ⊆ whitneyRootPartition Q H)
  (hbad : ∀ V ∈ S, ω ∈ cellFailure M τ η V)

def stoppedKuhnFluxPotential (q : Vec 2) : H1Function (openCubeSet Q) :=
  q 1 • stoppedGlobalKuhnCorrection M Q H hH τ η ω hgood S hS hbad 0-
    q 0 • stoppedGlobalKuhnCorrection M Q H hH τ η ω hgood S hS hbad 1

theorem stopped_kuhn_flux_potential_memH10 (q : Vec 2) :
    MemH10 (openCubeSet Q) (stoppedKuhnFluxPotential M Q H hH τ η ω hgood S hS hbad q).toFun := by
  simp only [stoppedKuhnFluxPotential,H1Function.sub_toFun,H1Function.smul_toFun]
  exact memH10_sub
    (memH10_smul (q 1) (stopped_global_kuhn_correction_memH10 M Q H hH τ η ω hgood S hS hbad 0))
    (memH10_smul (q 0) (stopped_global_kuhn_correction_memH10 M Q H hH τ η ω hgood S hS hbad 1))

/-- Literal source antisymmetric-potential flux, with the fixed divergence
convention. This identity is pointwise for the chosen weak representatives. -/
theorem stopped_kuhn_flux_source (q : Vec 2) (x : Vec 2) :
    matVecMul (planarFluxMatrix (stoppedKuhnGradient M Q H hH τ η ω hgood S hS hbad x)) q-q=
      matVecMul responsePlanarJ ((stoppedKuhnFluxPotential M Q H hH τ η ω hgood S hS hbad q).grad x) := by
  rw [planar_flux_matrix_apply]
  simp only [stoppedKuhnGradient,stoppedKuhnMidpointCoordinate,H1Function.add_grad,Pi.add_apply,
    stoppedKuhnFluxPotential,H1Function.sub_grad,H1Function.smul_grad,
    diagAffineLinear,LinearMap.coe_mk,AddHom.coe_mk,H1Function.affineOnIsSobolevRegularDomain_grad]
  funext i
  fin_cases i <;> simp [matVecMul,responsePlanarJ,Fin.sum_univ_two,basisVec] <;> ring

/-- The flux correction lies in the actual parent response space and has
zero normal trace. No face compatibility or flux-admissibility premise remains. -/
theorem stopped_kuhn_flux_admissible (q : Vec 2) :
    MemVectorL2 (openCubeSet Q)
      (fun x => matVecMul (planarFluxMatrix (stoppedKuhnGradient M Q H hH τ η ω hgood S hS hbad x)) q-q) ∧
    IsSolenoidalZeroNormalTraceOn (openCubeSet Q)
      (fun x => matVecMul (planarFluxMatrix (stoppedKuhnGradient M Q H hH τ η ω hgood S hS hbad x)) q-q) := by
  have he : (fun x => matVecMul (planarFluxMatrix (stoppedKuhnGradient M Q H hH τ η ω hgood S hS hbad x)) q-q)=
      fun x => matVecMul responsePlanarJ ((stoppedKuhnFluxPotential M Q H hH τ η ω hgood S hS hbad q).grad x) :=
    funext (stopped_kuhn_flux_source M Q H hH τ η ω hgood S hS hbad q)
  rw [he]
  exact rotated_h10_gradient_admissible (isOpen_openCubeSet Q)
    (stoppedKuhnFluxPotential M Q H hH τ η ω hgood S hS hbad q)
    (stopped_kuhn_flux_potential_memH10 M Q H hH τ η ω hgood S hS hbad q)

end
end ASDExplicitGamma.Inverse
