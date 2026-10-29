module

public import ASDExplicitGamma.Variational.LocalizedRowOperator

/-! Literal source-row characterization of the bounded affine-gradient operator. -/

@[expose] public section
namespace ASDExplicitGamma.Variational
open Homogenization MeasureTheory ASDExplicitGamma.Triadic
open scoped ENNReal
noncomputable section

 theorem localizedRowOperator_apply_ae (Q : TriadicCube 2)
    (I : H1Function (openCubeSet Q) →ₗ[ℝ] H1Function (openCubeSet Q))
    (η : H1Function (openCubeSet Q))
    (hη : MemLp η.toFun ⊤ (volume.restrict (openCubeSet Q)))
    (hDη : ∀ i, MemLp (fun x => η.grad x i) ⊤ (volume.restrict (openCubeSet Q)))
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hI : ∀ v ∈ affinePotentialSubmodule Q, ‖(I v).gradToHilbertVectorL2‖ ≤ A*‖v.gradToHilbertVectorL2‖)
    (hR : ∀ v ∈ affinePotentialSubmodule Q, ‖(v-I v).toScalarL2‖ ≤ B*‖v.gradToHilbertVectorL2‖)
    (v : affinePotentialSubmodule Q) :
    localizedRowOperator Q I η hη hDη hA hB hI hR (affineGradientRangeMap Q v) =ᵐ[volume.restrict (openCubeSet Q)]
      fun x => HilbertVec.ofVec (lemmaVPlanarRowField I η v x) := by
  let μ := volume.restrict (openCubeSet Q)
  let a := hη.toLp η.toFun
  let b := weakColumnDivergenceLp η hDη
  let X := (I v).gradToHilbertVectorL2
  let Y := ((v : H1Function _)-I v).toScalarL2
  let J := hilbertPlanarJ.toContinuousLinearMap.compLpL 2 μ
  let MX := lpScalarMultiplication μ a (J X)
  let MY := lpVectorMultiplication μ b Y
  have he : localizedRowOperator Q I η hη hDη hA hB hI hR (affineGradientRangeMap Q v) = MX+MY := by
    simp only [localizedRowOperator, add_apply, ContinuousLinearMap.comp_apply,
      (interpolantGradientOperator_spec Q I hA hI).2 v, (interpolantResidualOperator_spec Q I hB hR).2 v]
    rfl
  rw [he]
  filter_upwards [Lp.coeFn_add MX MY,
    lpScalarMultiplication_apply_ae μ a (J X), lpVectorMultiplication_apply_ae μ b Y,
    hilbertPlanarJ.toContinuousLinearMap.coeFn_compLpL X, hη.coeFn_toLp,
    (weakColumnDivergence_memLp_top η hDη).coeFn_toLp,
    (I v).coeFn_gradToHilbertVectorL2, ((v : H1Function _)-I v).coeFn_toScalarL2]
    with x hadd hmx hmy hj ha hb hx hy
  rw [hadd]
  simp only [Pi.add_apply, MX, MY, a, b, J, X, Y] at hmx hmy hj ha hb hx hy ⊢
  simp only [weakColumnDivergenceLp] at hmy hb ⊢
  rw [hmx,hmy,hj,ha,hb,hx,hy]
  apply HilbertVec.ext
  intro i
  rfl

end
end ASDExplicitGamma.Variational
