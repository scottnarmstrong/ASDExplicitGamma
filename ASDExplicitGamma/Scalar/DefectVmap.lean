module

public import ASDExplicitGamma.Scalar.PhysicalResolventParity
public import ASDExplicitGamma.Scalar.FlatResolvent

/-! The physical insertion `H ↦ V_H` and the flat potential carrier as continuous linear maps. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian
open scoped InnerProductSpace

noncomputable section

theorem projectedCoefficient_continuous (Q : TriadicCube 2) (σ : ℝ) (hσ : 0 < σ) :
    Continuous (fun k : ResponseCoefficient (openCubeSet Q) =>
      physicalProjectedCoefficient Q σ hσ k) := by
  have hS : Continuous (fun k : ResponseCoefficient (openCubeSet Q) =>
      responseShearL2Operator σ hσ k) :=
    (responseShearL2Family (measurableSet_openCubeSet Q) σ hσ).continuous
  fun_prop [physicalProjectedCoefficient, physicalPositiveShear,
    responseShearL2Operator]

/-- The physical insertion as a continuous linear map of the response coefficient. -/
def vmap' (Q : TriadicCube 2) (σ : ℝ) (hσ : 0 < σ) :
    ResponseCoefficient (openCubeSet Q) →L[ℝ]
      ((physicalPotentialSpace Q).toSubmodule →L[ℝ] HilbertVectorL2 (openCubeSet Q)) :=
  AddMonoidHom.toRealLinearMap
    (AddMonoidHom.mk' (fun k => physicalProjectedCoefficient Q σ hσ k)
      (fun k H => physicalProjectedCoefficient_add Q σ hσ k H))
    (projectedCoefficient_continuous Q σ hσ)

theorem vmap_apply (Q : TriadicCube 2) (σ : ℝ) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) :
    vmap' Q σ hσ k = physicalProjectedCoefficient Q σ hσ k := rfl

theorem vmap_mem_flux (Q : TriadicCube 2) (σ : ℝ) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (x : (physicalPotentialSpace Q).toSubmodule) :
    vmap' Q σ hσ k x ∈ (physicalFluxSpace Q).toSubmodule :=
  ((physicalFluxSpace Q).toSubmodule.orthogonalProjectionOnto _).2

/-- The flat source potential carrier as a continuous linear map of the shell field. -/
def flCLM (Q : TriadicCube 2) {a₀ b₀ c₀ d₀ : ℝ} (hab : a₀ < b₀) (hcd : c₀ < d₀) (e : Vec 2) :
    C(closedRectangle a₀ b₀ c₀ d₀, ℝ) →L[ℝ] (physicalPotentialSpace Q).toSubmodule :=
  (lambda8Q3ProjectedLoadClass (isOpenBoundedConvexDomain_openCubeSet Q) a₀ b₀ c₀ d₀ hab hcd
    e).codRestrict (physicalPotentialSpace Q).toSubmodule
    (fun z => (flatSourcePotentialCarrier Q hab hcd e z).2)

end

end ASDExplicitGamma.Scalar
