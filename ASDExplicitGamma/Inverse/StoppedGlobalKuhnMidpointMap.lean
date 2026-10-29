module

public import ASDExplicitGamma.Inverse.StoppedGlobalKuhnCorrection

/-! A single loading-independent parent interpolant built from the actual
stopped groups. It supplies the exact affine H1_0 residual for the full
potential/flux lift. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3 Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Whitney ASDExplicitGamma.Triadic
noncomputable section

local instance stoppedKuhnMidpointFiniteVolume (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

variable (M : ABKModel 2) (Q : TriadicCube 2) (H : ℕ) (hH : 333 ≤ H)
  (τ η : ℝ) (ω : Cutoff.CutoffSample 2)
  (hgood : ∀ k, H ≤ k → ω ∉ separationFailure
    (q3PlanarMarks M (Q.scale-k) τ η) k (rootBlockStart Q k))
  (S : Set (TriadicCube 2)) (hS : S ⊆ whitneyRootPartition Q H)
  (hbad : ∀ V ∈ S, ω ∈ cellFailure M τ η V)

/-- The source coordinate map on the whole root. -/
def stoppedKuhnMidpointCoordinate (i : Fin 2) : H1Function (openCubeSet Q) :=
  diagAffineLinear Q (basisVec i)+stoppedGlobalKuhnCorrection M Q H hH τ η ω hgood S hS hbad i

/-- Every affine loading uses the same two source coordinate corrections. -/
def stoppedKuhnMidpointLoadLinear : Vec 2 →ₗ[ℝ] H1Function (openCubeSet Q) where
  toFun p := diagAffineLinear Q p+∑ i : Fin 2, p i • stoppedGlobalKuhnCorrection M Q H hH τ η ω hgood S hS hbad i
  map_add' p q := by
    simp only [Pi.add_apply,add_smul,LinearMap.map_add,Finset.sum_add_distrib]
    abel
  map_smul' a p := by
    change diagAffineLinear Q (a • p)+
      ∑ i : Fin 2, (a • p) i • stoppedGlobalKuhnCorrection M Q H hH τ η ω hgood S hS hbad i =
      a • (diagAffineLinear Q p+∑ i : Fin 2, p i • stoppedGlobalKuhnCorrection M Q H hH τ η ω hgood S hS hbad i)
    rw [LinearMap.map_smul]
    simp only [Pi.smul_apply,smul_eq_mul]
    rw [smul_add,Finset.smul_sum]
    simp only [smul_smul]

/-- The parent interpolant uses only the geometry and the mean-gradient load. -/
def stoppedKuhnMidpointLinearInterpolant :
    H1Function (openCubeSet Q) →ₗ[ℝ] H1Function (openCubeSet Q) :=
  (stoppedKuhnMidpointLoadLinear M Q H hH τ η ω hgood S hS hbad).comp (diagMeanGradientLinear Q)

theorem stopped_kuhn_midpoint_interpolant_residual_memH10
    (p : Vec 2) (r : H10Function (openCubeSet Q)) :
    MemH10 (openCubeSet Q)
      (ASDExplicitGamma.Variational.lemmaVAffinePotential
        (isOpenBoundedConvexDomain_openCubeSet Q) p r-
        stoppedKuhnMidpointLinearInterpolant M Q H hH τ η ω hgood S hS hbad
          (ASDExplicitGamma.Variational.lemmaVAffinePotential
            (isOpenBoundedConvexDomain_openCubeSet Q) p r)).toFun := by
  let c : H1Function (openCubeSet Q) := ∑ i : Fin 2,
    p i • stoppedGlobalKuhnCorrection M Q H hH τ η ω hgood S hS hbad i
  have hc : MemH10 (openCubeSet Q) c.toFun := by
    rw [show c=∑ i : Fin 2, p i • stoppedGlobalKuhnCorrection M Q H hH τ η ω hgood S hS hbad i from rfl,Fin.sum_univ_two]
    exact memH10_add
      (memH10_smul (p 0) (stopped_global_kuhn_correction_memH10 M Q H hH τ η ω hgood S hS hbad 0))
      (memH10_smul (p 1) (stopped_global_kuhn_correction_memH10 M Q H hH τ η ω hgood S hS hbad 1))
  have hI : stoppedKuhnMidpointLinearInterpolant M Q H hH τ η ω hgood S hS hbad
      (ASDExplicitGamma.Variational.lemmaVAffinePotential
        (isOpenBoundedConvexDomain_openCubeSet Q) p r)=diagAffineLinear Q p+c := by
    change stoppedKuhnMidpointLoadLinear M Q H hH τ η ω hgood S hS hbad
      (diagMeanGradientLinear Q (ASDExplicitGamma.Variational.lemmaVAffinePotential
        (isOpenBoundedConvexDomain_openCubeSet Q) p r)) = _
    rw [diagMeanGradient_affinePotential]
    rfl
  have hres := memH10_sub r.memH10 hc
  convert hres using 1
  rw [hI]
  simp only [ASDExplicitGamma.Variational.lemmaVAffinePotential,diagAffineLinear,
    LinearMap.coe_mk,AddHom.coe_mk,H1Function.sub_toFun,H1Function.add_toFun]
  funext x
  abel

end
end ASDExplicitGamma.Inverse
