module

public import ASDExplicitGamma.Scalar.FwIdentMain
public import ASDExplicitGamma.Scalar.PairedTwoSlotRep
public import ASDExplicitGamma.Scalar.DefectCfg

/-! Reference check (i), part 1: `V_H^* e = -σ⁻¹ F(H)` for the constant flux load `e`. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization ASDExplicitGamma.Response ASDExplicitGamma.Variational
  ASDExplicitGamma.Triadic ASDExplicitGamma.Gaussian MeasureTheory
open scoped InnerProduct InnerProductSpace

noncomputable section

local instance refFiniteMeasure (Q : TriadicCube 2) :
    MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

theorem ref_vecDot_J (c : ℝ) (p e : Vec 2) :
    vecDot (c • matVecMul responsePlanarJ p) e = -c * vecDot p (matVecMul responsePlanarJ e) := by
  simp [vecDot, matVecMul, responsePlanarJ, Fin.sum_univ_two]
  ring

/-- Inner product of a shear with the constant load, in plain terms. -/
theorem ref_inner_shear_const (Q : TriadicCube 2) (σ : ℝ) (hσ : 0 < σ)
    (H : ResponseCoefficient (openCubeSet Q)) (p : HilbertVectorL2 (openCubeSet Q)) (e : Vec 2) :
    ⟪physicalPositiveShear Q σ hσ H p, physicalConstantLoad Q e⟫_ℝ =
      ∫ y in openCubeSet Q, -(responseCoefficientExtension H y / σ) *
        vecDot (rep' p y) (matVecMul responsePlanarJ e) := by
  rw [inner_rep]
  have hW := fw_shear_toPlain_ae Q σ hσ H p
  have hc : hilbertVectorL2ToVectorL2 (physicalConstantLoad Q e) =ᵐ[volumeMeasureOn (openCubeSet Q)]
      fun _ => e := by
    unfold physicalConstantLoad
    rw [hilbertVectorL2ToVectorL2_toHilbertVectorL2]
    exact coeFn_toVectorL2 _
  refine integral_congr_ae ?_
  filter_upwards [hW, hc] with y h1 h2
  change vecDot (hilbertVectorL2ToVectorL2 (physicalPositiveShear Q σ hσ H p) y)
    (hilbertVectorL2ToVectorL2 (physicalConstantLoad Q e) y) = _
  rw [h1, h2, ref_vecDot_J]
  rfl

theorem ref_inner_flat_carrier (Q : TriadicCube 2) {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hQ : openCubeSet Q ⊆ openRectangle a b c d)
    (hQcl : closure (openCubeSet Q) ⊆ closedRectangle a b c d) (e : Vec 2)
    (z : C(closedRectangle a b c d, ℝ)) (x : (physicalPotentialSpace Q).toSubmodule) :
    ⟪(x : HilbertVectorL2 (openCubeSet Q)),
        (flatSourcePotentialCarrier Q hab hcd e z : HilbertVectorL2 (openCubeSet Q))⟫_ℝ =
      ∫ y in openCubeSet Q, responseCoefficientExtension
        (physicalResponseRestriction Q hQcl z) y *
        vecDot (rep' (x : HilbertVectorL2 (openCubeSet Q))  y) (matVecMul responsePlanarJ e) := by
  let U := openCubeSet Q
  let hDom := isOpenBoundedConvexDomain_openCubeSet Q
  have hxr : (x : HilbertVectorL2 U) ∈ (lambda8H10GradientRange hDom).toSubmodule :=
    ⟨potMap Q (x : HilbertVectorL2 U), potMap_gradient Q x⟩
  have hfield := lambda8Q3LoadField_memVectorL2 hDom.1.measurableSet a b c d hab hcd e z
  have h1 : (flatSourcePotentialCarrier Q hab hcd e z : HilbertVectorL2 U) =
      (lambda8H10GradientRange hDom).toSubmodule.starProjection
        (toHilbertVectorL2OfVecField hfield) := rfl
  rw [h1, ← Submodule.inner_starProjection_left_eq_right,
    (Submodule.starProjection_eq_self_iff).mpr hxr]
  conv_lhs => rw [← hilbert_rebuild (x : HilbertVectorL2 U)]
  rw [inner_ofField (rep_memL2 _) hfield]
  refine setIntegral_congr_fun hDom.1.measurableSet fun y hy => ?_
  have hyr : y ∈ openRectangle a b c d := hQ hy
  simp only [lambda8Q3LoadField]
  rw [lambda8CovarianceClamp_eq_of_mem a b c d hab hcd hyr, responseCoefficientExtension_eq _ hy]
  simp [vecDot, physicalResponseRestriction, Pi.smul_apply, Finset.mul_sum]
  ring

theorem ref_coe_inner (Q : TriadicCube 2) (x y : (physicalPotentialSpace Q).toSubmodule) :
    ⟪x, y⟫_ℝ = ⟪(x : HilbertVectorL2 (openCubeSet Q)), (y : HilbertVectorL2 (openCubeSet Q))⟫_ℝ :=
  rfl

/-- `V_H^* e = -σ⁻¹ F(H)` for the constant flux load. -/
theorem ref_Vstar (Q : TriadicCube 2) {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hQ : openCubeSet Q ⊆ openRectangle a b c d)
    (hQcl : closure (openCubeSet Q) ⊆ closedRectangle a b c d) (σ : ℝ) (hσ : 0 < σ)
    (e : Vec 2) (z : C(closedRectangle a b c d, ℝ)) :
    (physicalProjectedInsertion Q σ hσ (physicalResponseRestriction Q hQcl z)).adjoint
        (physicalConstantLoad Q e) =
      (-σ⁻¹) • flatSourcePotentialCarrier Q hab hcd e z := by
  refine ext_inner_left ℝ fun x => ?_
  have hs : ⟪x, (-σ⁻¹) • flatSourcePotentialCarrier Q hab hcd e z⟫_ℝ =
      (-σ⁻¹) * ⟪x, flatSourcePotentialCarrier Q hab hcd e z⟫_ℝ := by
    calc ⟪x, (-σ⁻¹) • flatSourcePotentialCarrier Q hab hcd e z⟫_ℝ
        = ⟪(x : HilbertVectorL2 (openCubeSet Q)),
            (((-σ⁻¹) • flatSourcePotentialCarrier Q hab hcd e z :
              (physicalPotentialSpace Q).toSubmodule) : HilbertVectorL2 (openCubeSet Q))⟫_ℝ :=
          ref_coe_inner Q _ _
      _ = (-σ⁻¹) * ⟪(x : HilbertVectorL2 (openCubeSet Q)),
            (flatSourcePotentialCarrier Q hab hcd e z : HilbertVectorL2 (openCubeSet Q))⟫_ℝ := by
          rw [Submodule.coe_smul, real_inner_smul_right]
      _ = _ := by rw [ref_coe_inner Q x (flatSourcePotentialCarrier Q hab hcd e z)]
  rw [ContinuousLinearMap.adjoint_inner_right, hs]
  have hproj : physicalProjectedInsertion Q σ hσ (physicalResponseRestriction Q hQcl z) x =
      ((physicalSolenoidalSpace Q).toSubmodule)ᗮ.starProjection
        (physicalPositiveShear Q σ hσ (physicalResponseRestriction Q hQcl z)
          (x : HilbertVectorL2 (openCubeSet Q))) :=
    fw_projCoeff_apply Q σ hσ _ x
  have he : physicalConstantLoad Q e ∈ ((physicalSolenoidalSpace Q).toSubmodule)ᗮ :=
    physicalConstantLoad_mem_fluxSpace Q e
  rw [hproj, Submodule.inner_starProjection_left_eq_right,
    (Submodule.starProjection_eq_self_iff).mpr he, ref_inner_shear_const]
  rw [ref_coe_inner Q x (flatSourcePotentialCarrier Q hab hcd e z), ref_inner_flat_carrier Q hab hcd hQ hQcl e z x]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only
  ring

end

end ASDExplicitGamma.Scalar
