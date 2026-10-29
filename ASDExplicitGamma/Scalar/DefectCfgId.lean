module

public import ASDExplicitGamma.Scalar.DefectCfg
public import ASDExplicitGamma.Scalar.DefectFinsum

/-! Identification of the mode pair `C_i δu_j` with the flux and potential source fields. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
open scoped InnerProductSpace BigOperators

noncomputable section

theorem fluxSource_congr (Q : TriadicCube 2) {F F' : Vec 2 → Vec 2} (h : F = F')
    (hF : MemVectorL2 (openCubeSet Q) F) (hF' : MemVectorL2 (openCubeSet Q) F') :
    fluxSource Q hF = fluxSource Q hF' := by subst h; rfl

theorem potSource_congr (Q : TriadicCube 2) {F F' : Vec 2 → Vec 2} (h : F = F')
    (hF : MemVectorL2 (openCubeSet Q) F) (hF' : MemVectorL2 (openCubeSet Q) F') :
    potSource Q hF = potSource Q hF' := by subst h; rfl

theorem adjoint_zero_apply {X Y : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y] (y : Y) :
    ContinuousLinearMap.adjoint (0 : X →L[ℝ] Y) y = 0 := by
  apply ext_inner_right ℝ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.zero_apply, inner_zero_right,
    inner_zero_left]

namespace Cfg''

variable (C : Cfg'')

theorem Hs_some (i : ℕ) (l : whiteBasisIndex) (hl : eOpt i = some l) :
    C.Hs i = q3H3RangeValue C.a C.b C.c C.d C.β C.L
      (q3H3RangeFactor C.a C.b C.c C.d C.β C.L (whiteBasis l)) := by
  unfold Hs q3H3Directions
  rw [enumerated_eq, hl]

theorem Hs_none (i : ℕ) (hl : eOpt i = none) : C.Hs i = 0 := by
  unfold Hs q3H3Directions
  rw [enumerated_eq, hl]
  simp

theorem hlink_mode (i : ℕ) (l : whiteBasisIndex) (hl : eOpt i = some l) :
    (mainQ3DirectionW2 C.Q C.amp C.L (whiteBasis l)).value.toFun =ᵐ[
      volumeMeasureOn (openCubeSet C.Q)]
      fun x => responseCoefficientExtension (C.Rest (C.Hs i)) x / C.σ := by
  rw [Hs_some C i l hl]
  exact hlink'' C.Q C.hab C.hcd C.hQcl C.β C.σ C.L (whiteBasis l)

theorem affine_zero' (Q : TriadicCube 2) (r : H10Function (openCubeSet Q)) :
    lemmaVAffinePotential (isOpenBoundedConvexDomain_openCubeSet Q) 0 r = r.toH1Function := by
  ext p
  · simp only [lemmaVAffinePotential, H1Function.add_toFun,
      H1Function.affineOnIsSobolevRegularDomain_apply]
    simp
  · simp only [lemmaVAffinePotential, H1Function.add_grad,
      H1Function.affineOnIsSobolevRegularDomain_grad]
    simp

theorem hres'' (Q : TriadicCube 2) (m : ℕ) (r : H10Function (openCubeSet Q)) :
    MemH10 (openCubeSet Q) (r.toH1Function - diagInterpolant Q m r.toH1Function).toFun := by
  have := diagInterpolant_affine_residual_memH10 Q m 0 r
  rwa [affine_zero'] at this

theorem fslot_core (i : ℕ) (l : whiteBasisIndex) (hio : eOpt i = some l)
    (r : H10Function (openCubeSet C.Q)) (x : C.Xs)
    (hxr : (x : HilbertVectorL2 (openCubeSet C.Q)) = r.toH1Function.gradToHilbertVectorL2)
    (hRw : MemVectorL2 (openCubeSet C.Q) (lemmaVPlanarRowField (diagInterpolant C.Q 134)
      (mainQ3DirectionW2 C.Q C.amp C.L (whiteBasis l)).value r.toH1Function)) :
    C.Vm (C.Hs i) x = fluxSource C.Q hRw := by
  rw [Vm_apply]
  have hres : MemH10 (openCubeSet C.Q)
      (r.toH1Function - diagInterpolant C.Q 134 r.toH1Function).toFun := hres'' C.Q 134 r
  have hlk := hlink_mode C i l hio
  exact fslot_identification C.Q C.σ C.hσ (C.Rest (C.Hs i))
    (mainQ3DirectionW2 C.Q C.amp C.L (whiteBasis l)) hlk
    (diagInterpolant C.Q 134) r x hxr hres hRw

theorem gslot_core (i : ℕ) (l : whiteBasisIndex) (hio : eOpt i = some l)
    (y : C.Ys) (hy : y ∈ (physicalFluxSpace C.Q).toSubmodule)
    (hG : MemVectorL2 (openCubeSet C.Q)
      (gSlotOpt C.nQ 134 C.amp C.L (some l) (rep2 C.nQ 134 y)).1) :
    -(ContinuousLinearMap.adjoint (C.Vm (C.Hs i))) y = potSource C.Q hG := by
  rw [Vm_apply]
  have hlk := hlink_mode C i l hio
  have key := gslot_identification C.nQ 134 C.amp C.L C.σ C.hσ (C.Rest (C.Hs i)) l hlk y hy
  rw [key]
  exact potSource_congr C.Q rfl _ hG

end Cfg''

end

end ASDExplicitGamma.Scalar
