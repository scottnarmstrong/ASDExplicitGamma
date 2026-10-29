module

public import ASDExplicitGamma.Inverse.StoppedKuhnFinalMesh
public import ASDExplicitGamma.Inverse.StoppedKuhnGradientCharge

/-! The actual common gradient is constant on each simplex of the final
conforming Whitney mesh. Both source groups are restricted to that same
simplex; no loading-dependent mesh or gradient field is selected. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory ASDExplicitGamma.Triadic
open Algsuperdiff.Section3 Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Affine Algsuperdiff.Section3.Provider.Whitney
noncomputable section

variable (M : ABKModel 2) (Q : TriadicCube 2) (H : ℕ) (hH : 333 ≤ H)
  (τ η : ℝ) (ω : Cutoff.CutoffSample 2)
  (hgood : ∀ k, H ≤ k → ω ∉ separationFailure
    (q3PlanarMarks M (Q.scale-k) τ η) k (rootBlockStart Q k))
  (S : Set (TriadicCube 2)) (hS : S ⊆ whitneyRootPartition Q H)
  (hbad : ∀ V ∈ S, ω ∈ cellFailure M τ η V)

theorem stopped_kuhn_gradient_constant_on_final_simplex
    (n : ℕ) (P : TriadicCube 2) (hP : P ∈ whitneyRootLayer Q H n)
    (U : KuhnCell 2) (hU : U ∈ finalWhitneyKuhnCells Q H n P) :
    ∃ F : Matrix (Fin 2) (Fin 2) ℝ, ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q),
      x ∈ U.openCarrier → stoppedKuhnGradient M Q H hH τ η ω hgood S hS hbad x=F := by
  have hn := root_whitney_layer_pos Q H n hP
  have hnext : n-1+1=n := by omega
  have hrootU := final_kuhn_root_mem Q H n hP hU
  obtain ⟨Up,hUp,hUUp⟩ := final_kuhn_previous_parent Q H n hP hU
  have hUp' : Up ∈ rootKuhnMesh Q (compatibleWhitneyMeshDepth H (n-1+1)) := by
    simpa only [hnext] using hUp
  let fin0 := stopped_component_group_finite M Q H hH τ η ω hgood S hS hbad n
  let finp := stopped_component_group_finite M Q H hH τ η ω hgood S hS hbad (n-1)
  let ne0 := fun C : rootComponentGroup Q H S n =>
    stopped_component_group_nodes_nonempty M Q H hH τ η ω hgood S hS hbad n C.property
  let nep := fun C : rootComponentGroup Q H S (n-1) =>
    stopped_component_group_nodes_nonempty M Q H hH τ η ω hgood S hS hbad (n-1) C.property
  let D0 : Fin 2 → Vec 2 → ℝ := fun k => (rootGroupCorrection Q H S n fin0 ne0 k).toFun
  let Dp : Fin 2 → Vec 2 → ℝ := fun k => (rootGroupCorrection Q H S (n-1) finp nep k).toFun
  let F : Matrix (Fin 2) (Fin 2) ℝ := fun i k =>
    (1 : Matrix (Fin 2) (Fin 2) ℝ) i k+kuhnSlope U (D0 k) i+kuhnSlope Up (Dp k) i
  have hreps := ae_all_iff.mpr (fun i : Fin 2 => stopped_global_kuhn_correction_ae_two_groups M Q H hH τ η ω hgood S hS hbad i)
  refine ⟨F,?_⟩
  filter_upwards [hreps] with x hx
  intro hxU
  have hxP := final_kuhn_open_subset Q H n hP hU hxU
  ext i k
  have hg0 := root_kuhn_group_gradient_on_simplex M Q H hH τ η ω hgood S hS hbad n fin0 ne0 k i hrootU hxU
  have hgp := root_kuhn_group_gradient_on_simplex M Q H hH τ η ω hgood S hS hbad (n-1) finp nep k i hUp' (hUUp hxU)
  change (stoppedKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad k n).grad x i=kuhnSlope U (D0 k) i at hg0
  change (stoppedKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad k (n-1)).grad x i=kuhnSlope Up (Dp k) i at hgp
  change (diagAffineLinear Q (basisVec k)).grad x i+
    (stoppedGlobalKuhnCorrection M Q H hH τ η ω hgood S hS hbad k).grad x i=_
  rw [(hx k n P hP hxP).2 i,hg0,hgp]
  change basisVec k i+(kuhnSlope U (D0 k) i+kuhnSlope Up (Dp k) i)=_
  have hid : basisVec k i=(1 : Matrix (Fin 2) (Fin 2) ℝ) i k := by
    simp only [basisVec,Pi.single_apply,Matrix.one_apply]
  rw [hid]
  change _=(1 : Matrix (Fin 2) (Fin 2) ℝ) i k+kuhnSlope U (D0 k) i+kuhnSlope Up (Dp k) i
  ring

end
end ASDExplicitGamma.Inverse
