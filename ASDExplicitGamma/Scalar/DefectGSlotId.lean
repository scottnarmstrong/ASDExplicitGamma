module

public import ASDExplicitGamma.Scalar.DefectFSlotId
public import ASDExplicitGamma.Scalar.GSlotMeas2
public import ASDExplicitGamma.Scalar.PairedTwoSlotDuality

/-! G-slot identification: `-V_H^* y = Π_X G_l(y)` for `y` in the flux space. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
open scoped InnerProductSpace BigOperators

noncomputable section

theorem integral_eq_vol_avg (Q : TriadicCube 2) (m : ℕ) {F g : Vec 2 → Vec 2}
    (hF : MemVectorL2 (openCubeSet Q) F) (hg : MemVectorL2 (openCubeSet Q) g)
    (hFt : ∀ R ∈ descendantsAtDepth Q m, ∀ i : Fin 2,
      MemLp (fun x => F x i) 2 (normalizedCubeMeasure R))
    (hgt : ∀ R ∈ descendantsAtDepth Q m, ∀ i : Fin 2,
      MemLp (fun x => g x i) 2 (normalizedCubeMeasure R)) :
    ∫ z in openCubeSet Q, vecDot (F z) (g z) ∂volume =
      (volume (openCubeSet Q)).toReal *
        descendantsAverage Q m (fun R => vectorPairing R F g) := by
  have hint : IntegrableOn (fun z => vecDot (F z) (g z)) (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2 hF hg
  rw [integral_eq_vol_mul_avg Q m hint]
  congr 1
  unfold descendantsAverage
  dsimp only
  congr 1
  refine Finset.sum_congr rfl fun R hR => ?_
  rw [← lemmaV_cubeAverage_vecDot_eq_vectorPairing R (fun i => hFt R hR i)
    (fun i => hgt R hR i), cubeAverage_eq_integralAverage_openCubeSet R]
  rfl

/-- A closed-graph point of an `H¹₀` function. -/
def zOfH10 (U : Set (Vec 2)) (r : H10Function U) : H10GraphClosedSpace U :=
  ⟨(r.toH1Function.toScalarL2, r.toH1Function.gradToHilbertVectorL2),
    (h10GraphSubmodule U).le_topologicalClosure (h10_pair_mem_h10GraphSubmodule r)⟩

section Ident

variable (nQ : ℤ) (m : ℕ) (b : ℝ) (L : {l : ℝ // 0 < l})

local notation "QQ" => originCube 2 nQ

theorem rowElt_memL2 (l : whiteBasisIndex) (r : H10Function (openCubeSet QQ)) :
    MemVectorL2 (openCubeSet QQ) (rowField QQ m b L l r) := by
  let η := mainQ3DirectionW2 QQ b L (whiteBasis l)
  have hη : MemLp η.value.toFun ⊤ (volume.restrict (openCubeSet QQ)) := η.value_memLp_top
  have hDη : ∀ i, MemLp (fun p => η.value.grad p i) ⊤ (volume.restrict (openCubeSet QQ)) :=
    fun i => PlanarW2Infinity.gradient_memLp_top_volume η i
  exact (lemmaVPlanarRowField_memL2 (diagInterpolant QQ m) η.value r.toH1Function hη hDη).neg

theorem gslot_identification (σ : ℝ) (hσ : 0 < σ)
    (H : ResponseCoefficient (openCubeSet QQ)) (l : whiteBasisIndex)
    (hlink : (mainQ3DirectionW2 QQ b L (whiteBasis l)).value.toFun =ᵐ[
        volumeMeasureOn (openCubeSet QQ)] fun x => responseCoefficientExtension H x / σ)
    (y : HilbertVectorL2 (openCubeSet QQ))
    (hy : y ∈ (physicalFluxSpace QQ).toSubmodule) :
    -((physicalProjectedInsertion QQ σ hσ H).adjoint y) =
      potSource QQ (gSlot_memL2 nQ m b L l (rep2 nQ m y)) := by
  classical
  let U := openCubeSet QQ
  apply ext_inner_right ℝ
  intro x
  obtain ⟨r0, hr0⟩ := x.2
  let z := zOfH10 U r0
  let r := rep'' nQ z
  have hxr : (x : HilbertVectorL2 U) = r.toH1Function.gradToHilbertVectorL2 := by
    rw [rep_class]
    exact hr0.symm
  let η := mainQ3DirectionW2 QQ b L (whiteBasis l)
  have hη : MemLp η.value.toFun ⊤ (volume.restrict U) := η.value_memLp_top
  have hDη : ∀ i, MemLp (fun p => η.value.grad p i) ⊤ (volume.restrict U) :=
    fun i => PlanarW2Infinity.gradient_memLp_top_volume η i
  have hRw := lemmaVPlanarRowField_memL2 (diagInterpolant QQ m) η.value r.toH1Function hη hDη
  have hres : MemH10 U (r.toH1Function - diagInterpolant QQ m r.toH1Function).toFun := by
    have := diagInterpolant_affine_residual_memH10 QQ m 0 r
    rwa [affine_zero] at this
  have hVx := fslot_identification QQ σ hσ H η hlink (diagInterpolant QQ m) r x hxr hres hRw
  let G := gSlot nQ m b L l (rep2 nQ m y)
  have hG := gSlot_memL2 nQ m b L l (rep2 nQ m y)
  rw [inner_neg_left, ContinuousLinearMap.adjoint_inner_left, hVx]
  change -⟪y, (fluxSource QQ hRw : HilbertVectorL2 U)⟫_ℝ =
    ⟪(potSource QQ hG : HilbertVectorL2 U), (x : HilbertVectorL2 U)⟫_ℝ
  rw [potSource_inner QQ hG x, real_inner_comm (fluxSource QQ hRw : HilbertVectorL2 U) y,
    fluxSource_inner QQ hRw y hy]
  have e1 : ⟪toHilbertVectorL2OfVecField hRw, y⟫_ℝ =
      ∫ z in U, vecDot (lemmaVPlanarRowField (diagInterpolant QQ m) η.value r.toH1Function z)
        (rep' y z) ∂volume := by
    have := inner_ofField hRw (rep_memL2 y)
    rwa [hilbert_rebuild y] at this
  have e2 : ⟪toHilbertVectorL2OfVecField hG, (x : HilbertVectorL2 U)⟫_ℝ =
      ∫ z in U, vecDot (G.1 z) (rep' (x : HilbertVectorL2 U) z) ∂volume := by
    have := inner_ofField hG (rep_memL2 (x : HilbertVectorL2 U))
    rwa [hilbert_rebuild (x : HilbertVectorL2 U)] at this
  have hx : hilbertVectorL2ToVectorL2 (x : HilbertVectorL2 U) =ᵐ[volumeMeasureOn U]
      r.toH1Function.grad := by
    rw [hxr]
    filter_upwards [coeFn_hilbertVectorL2ToVectorL2 r.toH1Function.gradToHilbertVectorL2,
      r.toH1Function.coeFn_gradToHilbertVectorL2] with z h1 h2
    rw [h1, h2]
    simp [hilbertifyVecField]
  have e3 : ∫ z in U, vecDot (G.1 z) (rep' (x : HilbertVectorL2 U) z) ∂volume =
      ∫ z in U, vecDot (G.1 z) (r.toH1Function.grad z) ∂volume := by
    refine integral_congr_ae ?_
    filter_upwards [hx] with z hz
    change vecDot (G.1 z) ((hilbertVectorL2ToVectorL2 (x : HilbertVectorL2 U) : Vec 2 → Vec 2) z) = _
    rw [hz]
  have e4 := integral_eq_vol_avg QQ m hG r.toH1Function.grad_memVectorL2
    (fun R hR i => (G.2 R hR i).1) (fun R hR i => grad_memLp_tile nQ m r hR i)
  have e5 := gSlot_dual nQ m b L l (rep2 nQ m y) z
  have hRowF := rowElt_memL2 nQ m b L l r
  have e6 := integral_eq_vol_avg QQ m hRowF (rep_memL2 y)
    (fun R hR i => (rowElt QQ m b L l r).2 R hR i |>.1)
    (fun R hR i => (rep2 nQ m y).2 R hR i)
  rw [e1, e2, e3, e4]
  change _ = (volume U).toReal * descendantsAverage QQ m (fun R => vectorPairing R G.1
        (rep'' nQ z).toH1Function.grad)
  rw [e5]
  have e7 : ∫ z in U, vecDot ((rowElt QQ m b L l r).1 z) (rep' y z) ∂volume =
      -∫ z in U, vecDot (lemmaVPlanarRowField (diagInterpolant QQ m) η.value r.toH1Function z)
        (rep' y z) ∂volume := by
    rw [← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    change vecDot (-lemmaVPlanarRowField (diagInterpolant QQ m) η.value r.toH1Function z)
      (rep' y z) = _
    simp [vecDot, Finset.sum_neg_distrib]
  change _ = (volume U).toReal * descendantsAverage QQ m (fun R => vectorPairing R
    (rowElt QQ m b L l r).1 (rep' y))
  have e6' : (volume U).toReal * descendantsAverage QQ m (fun R => vectorPairing R
      (rowElt QQ m b L l r).1 (rep' y)) =
      ∫ z in U, vecDot ((rowElt QQ m b L l r).1 z) (rep' y z) ∂volume := e6.symm
  rw [e6', e7]

end Ident

end

end ASDExplicitGamma.Scalar
