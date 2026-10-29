module

public import ASDExplicitGamma.Inverse.StoppedKuhnScalarBounds

/-! Exact affine recovery for the source midpoint correction on one Kuhn
simplex, retaining both the value and the constant slope. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization
open Algsuperdiff.Section3.Provider.Affine Algsuperdiff.Section3.Provider.Whitney
noncomputable section

theorem kuhn_midpoint_affine_recovery (T : KuhnCell 2) (g : Vec 2 → ℝ)
    (c : ℝ) (i : Fin 2) (hg : ∀ v : Fin 3, g (T.vertex v)=c-T.vertex v i) :
    kuhnSlope T g= -basisVec i ∧ ∀ x, kuhnInterp T g x=c-x i := by
  have hv : ∀ v : Fin 3, g (T.vertex v)=(fun y => c-linearFn (basisVec i) y) (T.vertex v) := by
    intro v
    simpa only [linearFn,vecDot_basisVec_left] using hg v
  have hs := kuhnSlope_congr T (g := g) (g' := fun y => c-linearFn (basisVec i) y) hv
  have hc : kuhnSlope T (fun _ : Vec 2 => c)=0 :=
    kuhnSlope_eq_zero_of_vertex_const T (fun _ => rfl)
  rw [kuhnSlope_sub,hc,kuhnSlope_linearFn,zero_sub] at hs
  refine ⟨hs,?_⟩
  intro x
  rw [kuhnInterp_apply,hg 0,hs,vecDot_neg_left,vecDot_basisVec_left]
  simp only [Pi.sub_apply]
  ring

end
end ASDExplicitGamma.Inverse
