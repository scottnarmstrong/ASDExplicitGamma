module

public import ASDExplicitGamma.Native.OldSignedPlanarProjection

/-! The local Dirichlet projection agrees on the actual whole-plane
projected mode and its original q3 source. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Scalar
noncomputable section

/-- An actual solenoidal difference has zero projection on every local
Dirichlet gradient, with no projection equality assumed. -/
theorem old_signed_dirichlet_projection_eq_of_solenoidal
    {d : ℕ} [NeZero d] {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {F H : Vec d → Vec d} (hF : MemVectorL2 U F) (hH : MemVectorL2 U H)
    (hsol : IsSolenoidalOn U (fun x => F x-H x)) :
    lambda8DirichletProjection hU (toHilbertVectorL2OfVecField hF)=
      lambda8DirichletProjection hU (toHilbertVectorL2OfVecField hH) := by
  apply lambda8DirichletProjection_eq_of_orthogonal hU _ _
  intro y hy
  rcases hy with ⟨z,hz⟩
  change H10GraphClosed.gradientCLM (U := U) z=y at hz
  obtain ⟨u,_,hugrad⟩ := exists_h10Function_of_mem_h10GraphClosedSubmodule
    (U := U) hU (z := z.1) z.2
  have hgrad : u.toH1Function.gradToHilbertVectorL2=H10GraphClosed.gradientCLM (U := U) z := by
    simpa [H10GraphClosed.gradientCLM] using hugrad
  have hygrad := hgrad.trans hz
  rw [←toHilbertVectorL2OfVecField_sub hF hH,←hygrad]
  exact (inner_toHilbertVectorL2OfVecField_eq_integral (hF.sub hH)
    u.toH1Function.grad_memVectorL2).trans (hsol u)

/-- The unprojected actual q3 load also has finite local energy, with no
integrability witness assumed from the eventual native source theorem. -/
theorem old_signed_physical_raw_load_memL2 (Q : TriadicCube 2) (b : ℝ) (L : {l : ℝ // 0 < l})
    (w : WhiteNoise) (j : Fin 2) :
    MemVectorL2 (openCubeSet Q) (fun x => q3Convolution b L h3Zero w x • basisVec j) := by
  let u := H1Function.ofContDiffOnIsOpenBoundedConvexDomain (isOpenBoundedConvexDomain_openCubeSet Q)
    (q3Convolution_contDiff_one b L h3Zero (by norm_num [h3Zero,H3Index]) w)
  exact ((ContinuousLinearMap.id ℝ ℝ).smulRight (basisVec j)).comp_memLp' u.memL2

end
end ASDExplicitGamma.Native
