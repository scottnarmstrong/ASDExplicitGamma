module

public import ASDExplicitGamma.Variational.AffineGradientClosed
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Algebra.Module.Projective

/-! A uniquely characterized bounded map descended through a surjective gradient map. -/

@[expose] public section
namespace ASDExplicitGamma.Variational
noncomputable section

 theorem existsUnique_bounded_factor {P G F : Type*} [AddCommGroup P] [Module ℝ P]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : P →ₗ[ℝ] G) (hg : Function.Surjective g) (f : P →ₗ[ℝ] F) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ p, ‖f p‖ ≤ C*‖g p‖) :
    ∃! L : G →L[ℝ] F, ‖L‖ ≤ C ∧ ∀ p, L (g p)=f p := by
  obtain ⟨s,hs⟩ := g.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hg)
  have hgs (x : G) : g (s x)=x := LinearMap.congr_fun hs x
  let l := f.comp s
  have hl (p : P) : l (g p)=f p := by
    have hz : g (s (g p)-p)=0 := by rw [map_sub,hgs,sub_self]
    have hn := hb (s (g p)-p)
    rw [hz,norm_zero,mul_zero] at hn
    have hf0 : f (s (g p)-p)=0 := norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))
    simpa only [l, LinearMap.comp_apply, map_sub,sub_eq_zero] using hf0
  have hbound (x : G) : ‖l x‖ ≤ C*‖x‖ := by
    simpa only [l, LinearMap.comp_apply, hgs] using hb (s x)
  let L := l.mkContinuous C hbound
  refine ⟨L,⟨LinearMap.mkContinuous_norm_le l hC hbound,hl⟩,?_⟩
  rintro L' ⟨_,hL'⟩
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨p,rfl⟩ := hg x
  exact (hL' p).trans (hl p).symm

/-- The actual gradient map onto its exact closed source range is surjective. -/
def affineGradientRangeMap (Q : Homogenization.TriadicCube 2) :
    affinePotentialSubmodule Q →ₗ[ℝ] affineGradientClosedSubmodule Q where
  toFun v := ⟨h1GradientLinearMap (Homogenization.openCubeSet Q) v,⟨v,v.property,rfl⟩⟩
  map_add' x y := by
    apply Subtype.ext
    change (h1GradientLinearMap (Homogenization.openCubeSet Q)) ((x : Homogenization.H1Function (Homogenization.openCubeSet Q))+y) = (h1GradientLinearMap (Homogenization.openCubeSet Q)) x + (h1GradientLinearMap (Homogenization.openCubeSet Q)) y
    exact (h1GradientLinearMap (Homogenization.openCubeSet Q)).map_add x y
  map_smul' c x := by
    apply Subtype.ext
    change (h1GradientLinearMap (Homogenization.openCubeSet Q)) (c • (x : Homogenization.H1Function (Homogenization.openCubeSet Q))) = c • (h1GradientLinearMap (Homogenization.openCubeSet Q)) x
    exact (h1GradientLinearMap (Homogenization.openCubeSet Q)).map_smul c x

 theorem affineGradientRangeMap_surjective (Q : Homogenization.TriadicCube 2) :
    Function.Surjective (affineGradientRangeMap Q) := by
  rintro ⟨F,v,hv,hF⟩
  refine ⟨⟨v,hv⟩,?_⟩
  apply Subtype.ext
  change (h1GradientLinearMap (Homogenization.openCubeSet Q)) v = F
  exact hF

end
end ASDExplicitGamma.Variational
