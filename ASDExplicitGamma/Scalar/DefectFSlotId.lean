module

public import ASDExplicitGamma.Scalar.PairedTwoSlotBound
public import ASDExplicitGamma.Scalar.PairedTwoSlotShear
public import ASDExplicitGamma.Scalar.DefectPosHaarFields

/-! F-slot identification: the physical insertion applied to a potential gradient is the flux
projection of the Lemma V row field. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational
open scoped InnerProductSpace

noncomputable section

local instance fsFinite (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

theorem fslot_identification (Q : TriadicCube 2) (σ : ℝ) (hσ : 0 < σ)
    (H : ResponseCoefficient (openCubeSet Q)) (η : PlanarW2Infinity Q)
    (hlink : η.value.toFun =ᵐ[volumeMeasureOn (openCubeSet Q)]
      fun x => responseCoefficientExtension H x / σ)
    (I : H1Function (openCubeSet Q) →ₗ[ℝ] H1Function (openCubeSet Q))
    (r : H10Function (openCubeSet Q))
    (xr : (physicalPotentialSpace Q).toSubmodule)
    (hxr : (xr : HilbertVectorL2 (openCubeSet Q)) = r.toH1Function.gradToHilbertVectorL2)
    (hres : MemH10 (openCubeSet Q) (r.toH1Function - I r.toH1Function).toFun)
    (hRw : MemVectorL2 (openCubeSet Q) (lemmaVPlanarRowField I η.value r.toH1Function)) :
    physicalProjectedInsertion Q σ hσ H xr =
      fluxSource Q hRw := by
  classical
  let U := openCubeSet Q
  have hη : MemLp η.value.toFun ⊤ (volume.restrict U) := η.value_memLp_top
  have hDη : ∀ i, MemLp (fun x => η.value.grad x i) ⊤ (volume.restrict U) :=
    fun i => PlanarW2Infinity.gradient_memLp_top_volume η i
  have hsol := lemmaV_lift_of_interpolant (isOpenBoundedConvexDomain_openCubeSet Q) I
    r.toH1Function η.value hres hη hDη
  have hskew := lemmaVPlanar_skewGradient_memL2 r.toH1Function hη
  have hdiff : MemVectorL2 U (fun x => η.value x •
      matVecMul ASDExplicitGamma.Response.responsePlanarJ (r.toH1Function.grad x) -
        lemmaVPlanarRowField I η.value r.toH1Function x) := hskew.sub hRw
  let K := (physicalFluxSpace Q).toSubmodule
  let P := K.orthogonalProjectionOnto
  let sh := physicalPositiveShear Q σ hσ H (xr : HilbertVectorL2 U)
  have hx : hilbertVectorL2ToVectorL2 (xr : HilbertVectorL2 U) =ᵐ[volumeMeasureOn U]
      r.toH1Function.grad := by
    rw [hxr]
    filter_upwards [coeFn_hilbertVectorL2ToVectorL2 r.toH1Function.gradToHilbertVectorL2,
      r.toH1Function.coeFn_gradToHilbertVectorL2] with x h1 h2
    rw [h1, h2]
    simp [hilbertifyVecField]
  have hlink' : ∀ᵐ x ∂(volumeMeasureOn U), η.value x = responseCoefficientExtension H x / σ := hlink
  have hshClass : sh = toHilbertVectorL2OfVecField hskew := by
    rw [← hilbert_rebuild sh]
    apply MeasureTheory.Lp.ext
    filter_upwards [coeFn_toHilbertVectorL2OfVecField (rep_memL2 sh),
      coeFn_toHilbertVectorL2OfVecField hskew,
      positiveShear_toPlain_ae Q σ hσ H (xr : HilbertVectorL2 U), hx, hlink'] with
      x h1 h2 h3 h4 h5
    rw [h1, h2]
    have : rep' sh x = η.value x • matVecMul ASDExplicitGamma.Response.responsePlanarJ
        (r.toH1Function.grad x) := by
      change (hilbertVectorL2ToVectorL2 sh : Vec 2 → Vec 2) x = _
      rw [h3, h4, h5]
    simp [hilbertifyVecField, this]
  have hsolMem : toHilbertVectorL2OfVecField hdiff ∈ (physicalSolenoidalSpace Q).toSubmodule := by
    change toHilbertVectorL2OfVecField hdiff ∈ PotentialSolenoidalExact.solenoidalZeroNormalTrace U
    rw [PotentialSolenoidalExact.mem_solenoidalZeroNormalTrace_iff]
    intro u
    rw [show u.gradToHilbertVectorL2 = toHilbertVectorL2OfVecField u.grad_memVectorL2 from rfl,
      inner_toHilbertVectorL2OfVecField_eq_integral hdiff u.grad_memVectorL2]
    exact hsol u
  have hPz : P (toHilbertVectorL2OfVecField hdiff) = 0 := by
    have hOrth : toHilbertVectorL2OfVecField hdiff ∈ Kᗮ := by
      change _ ∈ ((physicalSolenoidalSpace Q).toSubmoduleᗮ)ᗮ
      exact (physicalSolenoidalSpace Q).toSubmodule.le_orthogonal_orthogonal hsolMem
    exact K.orthogonalProjectionOnto_apply_of_mem_orthogonal hOrth
  have hsub : toHilbertVectorL2OfVecField hdiff =
      toHilbertVectorL2OfVecField hskew - toHilbertVectorL2OfVecField hRw :=
    toHilbertVectorL2OfVecField_sub hskew hRw
  have hPeq : P sh = P (toHilbertVectorL2OfVecField hRw) := by
    rw [hshClass]
    have := hPz
    rw [hsub, map_sub] at this
    exact sub_eq_zero.1 this
  change K.subtypeL (P sh) = K.subtypeL (P (toHilbertVectorL2OfVecField hRw))
  rw [hPeq]

end

end ASDExplicitGamma.Scalar
