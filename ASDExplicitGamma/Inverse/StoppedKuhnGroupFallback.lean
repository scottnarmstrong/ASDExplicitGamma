module

public import ASDExplicitGamma.Inverse.StoppedKuhnGroupFields
public import ASDExplicitGamma.Inverse.StoppedKuhnAE

/-! Uniform physical fallbacks of the actual Kuhn midpoint groups. Together
with their literal two-layer support they give the source finite-energy sum. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory ASDExplicitGamma.Triadic
open Algsuperdiff.Section3 Algsuperdiff.Section3.Provider
open Algsuperdiff.Section3.Provider.Affine Algsuperdiff.Section3.Provider.Whitney
noncomputable section

variable (M : ABKModel 2) (Q : TriadicCube 2)
    (H : ℕ) (hH : 333 ≤ H) (τ η : ℝ) (ω : Cutoff.CutoffSample 2)
    (hgood : ∀ k, H ≤ k → ω ∉ separationFailure
      (q3PlanarMarks M (Q.scale-k) τ η) k (rootBlockStart Q k))
    (S : Set (TriadicCube 2)) (hS : S ⊆ whitneyRootPartition Q H)
    (hbad : ∀ V ∈ S, ω ∈ cellFailure M τ η V)
    (a : ℕ) (hfin : (rootComponentGroup Q H S a).Finite)
    (hne : ∀ C : rootComponentGroup Q H S a,
      (componentMeshNodes Q (compatibleWhitneyMeshDepth H (a+1)) C.val).Nonempty)

theorem stopped_kuhn_group_value_fallback (i : Fin 2) (x : Vec 2) :
    |(rootKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad a hfin hne i).toFun x| ≤
      (3:ℝ)^(((a+whitneyProfile H a:ℕ):ℝ)/4)*(3:ℝ)^(Q.scale-((a+whitneyProfile H a:ℕ):ℤ)) := by
  classical
  let J := compatibleWhitneyMeshDepth H (a+1)
  let b := rootGroupNodalCorrection Q H S a hfin hne i
  by_cases ht : ∃ T ∈ rootKuhnMesh Q J, x ∈ T.closedCarrier
  · obtain ⟨T,hT,hxT⟩ := ht
    rw [root_kuhn_group_value_on_simplex M Q H hH τ η ω hgood S hS hbad a hfin hne i hT hxT]
    exact kuhn_interp_abs_bound T _ _
      (fun v => stopped_group_correction_value_fallback M Q H hH τ η ω hgood S hS hbad a hfin hne i (T.vertex v)) hxT
  · change |zeroExtendedKuhnAffine _ _ x| ≤ _
    rw [zeroExtendedKuhnAffine_of_forall_notMem (rootKuhnMesh Q J)
      (diagSynthesisH1Linear Q J b).toFun (by simpa only [not_exists,not_and] using ht),abs_zero]
    positivity

/-- Every actual chosen weak derivative obeys the same uniform source
coordinate payment almost everywhere on the root. -/
theorem stopped_kuhn_group_gradient_fallback (i k : Fin 2) :
    ∀ᵐ x ∂volume.restrict (openCubeSet Q),
      |(rootKuhnGroupCorrection M Q H hH τ η ω hgood S hS hbad a hfin hne i).grad x k| ≤
        18*(3:ℝ)^(((a+whitneyProfile H a:ℕ):ℝ)/4) := by
  let J := compatibleWhitneyMeshDepth H (a+1)
  let clock : ℝ := (3:ℝ)^(((a+whitneyProfile H a:ℕ):ℝ)/4)
  let side : ℝ := (3:ℝ)^(Q.scale-((a+whitneyProfile H a:ℕ):ℤ))
  filter_upwards [root_kuhn_ae_open_cover Q J] with x hx
  obtain ⟨T,hT,hxT⟩ := hx
  rw [root_kuhn_group_gradient_on_simplex M Q H hH τ η ω hgood S hS hbad a hfin hne i k hT hxT]
  have hh := kuhn_slope_abs_bound T (rootGroupCorrection Q H S a hfin hne i).toFun (clock*side)
    (fun v => stopped_group_correction_value_fallback M Q H hH τ η ω hgood S hS hbad a hfin hne i (T.vertex v)) k
  have hs : cubeScaleFactor T.supportCube=diagMeshRadius Q J := by
    change (3:ℝ)^T.supportCube.scale=diagMeshRadius Q J
    rw [root_kuhn_mesh_scale Q J hT,diag_mesh_radius_eq_zpow]
  rw [hs] at hh
  apply hh.trans
  apply (div_le_iff₀ (diagMeshRadius_pos Q J)).mpr
  have hm := mul_le_mul_of_nonneg_left (whitney_common_mesh_parent_side_le Q H a)
    (show 0 ≤ 2*clock by positivity)
  change 2*(clock*side) ≤ 18*clock*diagMeshRadius Q J
  nlinarith only [hm]

end
end ASDExplicitGamma.Inverse
