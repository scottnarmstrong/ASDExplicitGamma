module

public import ASDExplicitGamma.Inverse.PureFluxGeneratorActualSource
public import ASDExplicitGamma.Inverse.PureFluxGeneratorBankCentering

/-! The centered compact Gaussian directions and their actual response restrictions. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization ASDExplicitGamma.Gaussian ASDExplicitGamma.Main ASDExplicitGamma.Response
  ASDExplicitGamma.Triadic
noncomputable section

def pureFluxParentCenter (n : ℤ) : closure (cubeSet (originCube 2 n)) :=
  ⟨cubeCenter (originCube 2 n), subset_closure (openCubeSet_subset_cubeSet _ (by
    rw [← ball_cubeCenter_eq_openCubeSet]
    exact Metric.mem_ball_self (cubeRadius_pos _)))⟩

theorem pureFluxMainCubeQ3ResponseCoefficient_eq_restriction
    (n : ℤ) (b : ℝ) (L : {l : ℝ // 0 < l}) (j : ℕ) :
    pureFluxMainCubeQ3ResponseCoefficient n b L j =
      pureFluxOpenResponseRestriction n (pureFluxMainCubeQ3Directions n b L j) := by
  ext x
  rfl

theorem pureFluxMainCubeQ3CenteredResponseCoefficient_eq_restriction
    (n : ℤ) (b : ℝ) (L : {l : ℝ // 0 < l}) (j : ℕ) :
    pureFluxMainCubeQ3CenteredResponseCoefficient n b L j =
      pureFluxOpenResponseRestriction n
        (pureFluxCoefficientCentering (pureFluxParentCenter n)
          (pureFluxMainCubeQ3Directions n b L j)) := by
  rw [pureFluxCoefficientCentering_apply, map_sub]
  unfold pureFluxMainCubeQ3CenteredResponseCoefficient
  rw [pureFluxMainCubeQ3ResponseCoefficient_eq_restriction]
  have hcenter : pureFluxMainCubeQ3Directions n b L j (pureFluxParentCenter n) =
      q3Convolution b L h3Zero (gaussEnumerated whiteBasis j) (cubeCenter (originCube 2 n)) := by
    exact mainCubeH3Value_direction n b L j (pureFluxParentCenter n)
  rw [hcenter]
  ext x
  simp [sub_eq_add_neg, pureFluxOpenResponseRestriction,
    BoundedContinuousFunction.compContinuousCLM_apply,
    ContinuousMap.linearIsometryBoundedOfCompact_apply_apply]

/-- The actual centered response directions retain square summability. -/
theorem pureFluxMainCubeQ3CenteredResponseCoefficient_summable
    (n : ℤ) (b : ℝ) (L : {l : ℝ // 0 < l}) :
    Summable (fun j => ‖pureFluxMainCubeQ3CenteredResponseCoefficient n b L j‖^2) := by
  have hH : Summable (fun j => ‖pureFluxMainCubeQ3Directions n b L j‖^2) :=
    @summable_sq_bounded_image ℕ (MainCubeH3 n b L)
      C(closure (cubeSet (originCube 2 n)), ℝ)
      inferInstance (mainCubeH3InnerProductSpace n b L).toNormedSpace
      inferInstance inferInstance (mainCubeQ3Directions n b L)
      (mainCubeQ3Directions_summable n b L) (mainCubeH3Value n b L)
  have hc := summable_sq_bounded_image (pureFluxMainCubeQ3Directions n b L) hH
    (pureFluxCoefficientCentering (pureFluxParentCenter n))
  have hr := summable_sq_bounded_image (fun j =>
      pureFluxCoefficientCentering (pureFluxParentCenter n) (pureFluxMainCubeQ3Directions n b L j))
    hc (pureFluxOpenResponseRestriction n)
  simpa only [← pureFluxMainCubeQ3CenteredResponseCoefficient_eq_restriction] using hr

/-- Zero-padded Gaussian enumeration does not change any scalar contraction
that vanishes on the zero coefficient direction. -/
theorem pureFlux_centered_directions_tsum_apply (n : ℤ) (b : ℝ)
    (L : {l : ℝ // 0 < l})
    (f : ResponseCoefficient (openCubeSet (originCube 2 n)) → ℝ) (hf : f 0 = 0) :
    (∑' j, f (pureFluxMainCubeQ3CenteredResponseCoefficient n b L j)) =
      ∑' l : whiteBasisIndex, f (pureFluxMainCubeQ3CenteredResponseCoefficient n b L
        (@Encodable.encode whiteBasisIndex (Encodable.ofCountable whiteBasisIndex) l)) := by
  classical
  let enc := @Encodable.encode whiteBasisIndex (Encodable.ofCountable whiteBasisIndex)
  let v := fun l : whiteBasisIndex => pureFluxMainCubeQ3CenteredResponseCoefficient n b L (enc l)
  have hz (j : ℕ) (hj : j ∉ Set.range enc) :
      pureFluxMainCubeQ3CenteredResponseCoefficient n b L j = 0 := by
    rw [pureFluxMainCubeQ3CenteredResponseCoefficient_eq_restriction]
    have hdir : pureFluxMainCubeQ3Directions n b L j = 0 := by
      unfold pureFluxMainCubeQ3Directions mainCubeQ3Directions q3H3Directions
      rw [gaussEnumerated, Function.extend_apply' _ _ _ hj]
      exact map_zero _
    rw [hdir, map_zero, map_zero]
  have heq (j : ℕ) : pureFluxMainCubeQ3CenteredResponseCoefficient n b L j = gaussEnumerated v j := by
    by_cases hj : j ∈ Set.range enc
    · obtain ⟨l, rfl⟩ := hj
      rw [enumerated_encode]
    · rw [hz j hj, gaussEnumerated, Function.extend_apply' _ _ _ hj]
      rfl
  simp_rw [heq]
  simpa only [enumerated_encode] using enumerated_tsum_apply v f hf

end
end ASDExplicitGamma.Inverse
