module

public import ASDExplicitGamma.Scalar.PairLamSplit
public import ASDExplicitGamma.Scalar.PairBlock
public import ASDExplicitGamma.Scalar.DefectOldMaximizerDirectionalBot
public import ASDExplicitGamma.Scalar.OldCutoffCoefficient

/-! The flat flux defect `(x₀, y₀ − e)` of the final configuration is the flux-affine directional
pair of the OLD canonical field, and its tiled weak budget is `dirTiledBot`. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
  ASDExplicitGamma.Native
open Algsuperdiff.Section3
open scoped BigOperators

noncomputable section

theorem rest_old_eq (M : ABKModel 2) (K : Set (Vec 2)) [CompactSpace K] (ell m : ℤ)
    (hK : K ⊆ openCubeSet (originCube 2 ell)) (Q : TriadicCube 2)
    (hQcl : closure (openCubeSet Q) ⊆ K) (ω : Cutoff.CutoffSample 2) :
    physicalResponseRestriction Q hQcl (olderField K m ω) = oldCutoffSkewCoefficient m Q ω := by
  ext x
  have h1 : (physicalResponseRestriction Q hQcl (olderField K m ω)) x =
      olderField K m ω ⟨x.1, hQcl x.2⟩ := rfl
  have h2 := Gaussian.olderField_apply_eq_coefficientCutoff K M ell m hK ω ⟨x.1, hQcl x.2⟩
  rw [h1, h2]
  have h3 : (oldCutoffSkewCoefficient m Q ω) x = Cutoff.cutoff m ω x.1 1 0 := rfl
  rw [h3, Model.coefficientCutoff_eq_nu_add_cutoffValue]
  simp [Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)]
  rfl

theorem rep_sub_const (Q : TriadicCube 2) (Y : HilbertVectorL2 (openCubeSet Q)) (e : Vec 2) :
    rep' (Y - physicalConstantLoad Q e) =ᵐ[volumeMeasureOn (openCubeSet Q)]
      fun x i => rep' Y x i - e i := by
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  have hY := rep_memL2 Y
  have hc : MemVectorL2 (openCubeSet Q) (fun _ : Vec 2 => e) := memVectorL2_const e
  have hsub : MemVectorL2 (openCubeSet Q) (fun x i => rep' Y x i - e i) := hY.sub hc
  apply ae_of_toHilbert_eq (rep_memL2 _) hsub
  rw [hilbert_rebuild]
  have := toHilbertVectorL2OfVecField_sub hY hc
  change _ = toHilbertVectorL2OfVecField (hY.sub hc)
  rw [this, hilbert_rebuild]
  rfl

variable (M : ABKModel 2) (h : ℝ) (m : ℤ) {a b c d : ℝ} (hab : a < b) (hcd : c < d)
  (hQ : openCubeSet (originCube 2 (m + 129)) ⊆ openRectangle a b c d) (e : Vec 2)

/-- The flat flux defect `(x₀, y₀ − e)` has tiled weak budget `dirTiledBot`. -/
theorem final_flat_budget (ell : ℤ)
    (hK : closedRectangle a b c d ⊆ openCubeSet (originCube 2 ell)) (ω : Cutoff.CutoffSample 2) :
    let C := finalCfg M h m hab hcd hQ e
    let old := olderField (closedRectangle a b c d) m ω
    lemmaVTiledWeakEnergy C.Q 134 (rep'' C.nQ (potMap C.Q
          ((C.xIn old : C.Xs) : HilbertVectorL2 (openCubeSet C.Q)))).toH1Function.grad +
        lemmaVTiledWeakEnergy C.Q 134 (rep2 C.nQ 134 (C.yIn old)).1 =
      dirTiledBot M m C.Q e ω := by
  intro C old
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet C.Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet C.Q).isFiniteMeasure_restrict_volume
  have hrest : C.Rest old = oldCutoffSkewCoefficient m C.Q ω :=
    rest_old_eq M (closedRectangle a b c d) ell m hK C.Q C.hQcl ω
  obtain ⟨φ, η, hxφ, hyη, hS1, hS2⟩ := pair_flat_eq_canonical C.Q C.ν C.σ C.hν C.hσ
    (C.Rest old) C.e
  rw [hrest] at hS1 hS2
  have hxφ' : φ.toH1Function.gradToHilbertVectorL2 = ((C.xIn old : C.Xs) : HilbertVectorL2 (openCubeSet C.Q)) := hxφ
  have hpot := C.pot_ae (C.xIn old) φ hxφ'
  have hy1 : η.gradToHilbertVectorL2 = (C.U old).ofLp.1 := hyη
  have hflux := C.flux_ae ((C.U old).ofLp.1) η hy1
  have hprimal : (botPrimal M m C.Q C.e ω) =ᵐ[volumeMeasureOn (openCubeSet C.Q)] φ.toH1Function.grad :=
    hS1.mono fun x hx => hx.symm
  have hrec1 := rep_sub_const C.Q ((C.U old).ofLp.1) C.e
  have hrec2 : (fun x i => rep' ((C.U old).ofLp.1) x i - C.e i) =ᵐ[volumeMeasureOn (openCubeSet C.Q)]
      botRecip M m C.Q C.e ω := by
    filter_upwards [hflux, hS2] with x hx1 hx2
    funext i
    have h1 : rep' ((C.U old).ofLp.1) x = η.grad x := hx1
    rw [h1, hx2]
    rfl
  have hyrep : (rep2 C.nQ 134 (C.yIn old)).1 =ᵐ[volumeMeasureOn (openCubeSet C.Q)]
      botRecip M m C.Q C.e ω := hrec1.trans hrec2
  have hpr : (rep'' C.nQ (potMap C.Q ((C.xIn old : C.Xs) : HilbertVectorL2 (openCubeSet C.Q)))).toH1Function.grad
      =ᵐ[volumeMeasureOn (openCubeSet C.Q)] botPrimal M m C.Q C.e ω := hpot.trans (hprimal.symm)
  rw [tiledWeak_congr_ae C.Q 134 hpr, tiledWeak_congr_ae C.Q 134 hyrep]
  unfold dirTiledBot lemmaVTiledWeakEnergy
  rw [descendantsAverage_add]
  rfl

end

end ASDExplicitGamma.Scalar
