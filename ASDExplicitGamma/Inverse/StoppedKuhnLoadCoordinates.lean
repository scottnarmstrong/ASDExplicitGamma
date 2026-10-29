module

public import ASDExplicitGamma.Inverse.StoppedGlobalKuhnMidpointMap

/-! Every affine potential/flux loading uses the same actual two coordinate
maps. The coupling and zero-trace residual are exact H1 equalities. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory ASDExplicitGamma.Triadic
open Algsuperdiff.Section3 Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Whitney
noncomputable section

local instance stoppedKuhnLoadCoordinatesFiniteVolume (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

variable (M : ABKModel 2) (Q : TriadicCube 2) (H : ℕ) (hH : 333 ≤ H)
  (τ η : ℝ) (ω : Cutoff.CutoffSample 2)
  (hgood : ∀ k, H ≤ k → ω ∉ separationFailure
    (q3PlanarMarks M (Q.scale-k) τ η) k (rootBlockStart Q k))
  (S : Set (TriadicCube 2)) (hS : S ⊆ whitneyRootPartition Q H)
  (hbad : ∀ V ∈ S, ω ∈ cellFailure M τ η V)

theorem stopped_kuhn_load_coordinates (p : Vec 2) :
    stoppedKuhnMidpointLoadLinear M Q H hH τ η ω hgood S hS hbad p=
      ∑ i : Fin 2, p i • stoppedKuhnMidpointCoordinate M Q H hH τ η ω hgood S hS hbad i := by
  have hv : p=∑ i : Fin 2, p i • basisVec i := by
    funext k
    fin_cases k <;> simp [basisVec,Fin.sum_univ_two]
  have ha : diagAffineLinear Q p=∑ i : Fin 2, p i • diagAffineLinear Q (basisVec i) := by
    simpa only [map_sum,map_smul] using congrArg (diagAffineLinear Q) hv
  change diagAffineLinear Q p+(∑ i : Fin 2, p i • stoppedGlobalKuhnCorrection M Q H hH τ η ω hgood S hS hbad i)=
    ∑ i : Fin 2, p i • (diagAffineLinear Q (basisVec i)+stoppedGlobalKuhnCorrection M Q H hH τ η ω hgood S hS hbad i)
  simp_rw [smul_add]
  rw [Finset.sum_add_distrib,ha]

theorem stopped_kuhn_interpolant_affine_coordinates (p : Vec 2)
    (r : H10Function (openCubeSet Q)) :
    stoppedKuhnMidpointLinearInterpolant M Q H hH τ η ω hgood S hS hbad
      (ASDExplicitGamma.Variational.lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) p r)=
        ∑ i : Fin 2, p i • stoppedKuhnMidpointCoordinate M Q H hH τ η ω hgood S hS hbad i := by
  change stoppedKuhnMidpointLoadLinear M Q H hH τ η ω hgood S hS hbad
    (diagMeanGradientLinear Q (ASDExplicitGamma.Variational.lemmaVAffinePotential
      (isOpenBoundedConvexDomain_openCubeSet Q) p r))=_
  rw [diagMeanGradient_affinePotential]
  exact stopped_kuhn_load_coordinates M Q H hH τ η ω hgood S hS hbad p

theorem stopped_kuhn_coordinate_residual_memH10 (i : Fin 2) :
    MemH10 (openCubeSet Q)
      (stoppedKuhnMidpointCoordinate M Q H hH τ η ω hgood S hS hbad i-diagAffineLinear Q (basisVec i)).toFun := by
  have hh := stopped_global_kuhn_correction_memH10 M Q H hH τ η ω hgood S hS hbad i
  convert hh using 1
  funext x
  simp only [stoppedKuhnMidpointCoordinate,H1Function.sub_toFun,H1Function.add_toFun]
  ring

end
end ASDExplicitGamma.Inverse
