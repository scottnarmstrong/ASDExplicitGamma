module

public import ASDExplicitGamma.Model.BflatActualProjection
public import ASDExplicitGamma.Gaussian.RectangleDomain

/-! # Actual Dirichlet-mode observations of the B-flat field -/

@[expose] public section

open MeasureTheory Homogenization
open ASDExplicitGamma.Triadic
open scoped Topology RealInnerProductSpace

namespace ASDExplicitGamma.Model

theorem bflat_openSquare_eq_openRectangle :
    bflatSquareObservationDomain =
      Gaussian.openRectangle (-1/2) (1/2) (-1/2) (1/2) := by
  ext x
  simp [bflatSquareObservationDomain, bflatUnitSquare, Homogenization.openCubeSet,
    Gaussian.openRectangle, Homogenization.cubeScaleFactor]
  norm_num

theorem bflatClampReal_eq_self {x : ℝ} (hl : -1/2 ≤ x) (hr : x ≤ 1/2) :
    bflatClampReal x = x := by
  unfold bflatClampReal
  rw [min_eq_left hr, max_eq_right hl]

theorem bflatClampVec_eq_self_of_closed {x : Vec 2}
    (hx : x ∈ bflatClosedRectangle) : bflatClampVec x = x := by
  have hx' : x 0 ∈ Set.Icc (-1/2) (1/2) ∧ x 1 ∈ Set.Icc (-1/2) (1/2) := by
    simpa [bflatClosedRectangle, Gaussian.closedRectangle] using hx
  funext i
  fin_cases i
  · exact bflatClampReal_eq_self hx'.1.1 hx'.1.2
  · exact bflatClampReal_eq_self hx'.2.1 hx'.2.2

theorem bflatClampVec_eq_self_of_mem {x : Vec 2}
    (hx : x ∈ bflatSquareObservationDomain) : bflatClampVec x = x := by
  have hx' : x 0 ∈ Set.Ioo (-2⁻¹ : ℝ) (2⁻¹ : ℝ) ∧
      x 1 ∈ Set.Ioo (-2⁻¹ : ℝ) (2⁻¹ : ℝ) := by
    simpa [bflatSquareObservationDomain, bflatUnitSquare, Homogenization.openCubeSet,
      Homogenization.cubeScaleFactor] using hx
  apply bflatClampVec_eq_self_of_closed
  change x 0 ∈ Set.Icc (-1/2) (1/2) ∧ x 1 ∈ Set.Icc (-1/2) (1/2)
  constructor
  · constructor <;> norm_num at hx' ⊢ <;> linarith
  · constructor <;> norm_num at hx' ⊢ <;> linarith

theorem bflatObservation_eq_openSquare_integral
    (w f : C(bflatClosedRectangle, ℝ)) :
    bflatObservation w f =
      ∫ x : Vec 2 in bflatSquareObservationDomain,
        f (bflatClamp x) * w (bflatClamp x) := by
  rw [bflatObservation_apply]
  let F : Vec 2 → ℝ := fun x => f (bflatClamp x) * w (bflatClamp x)
  have hclosed : MeasurableSet
      (Gaussian.closedRectangle (-1/2) (1/2) (-1/2) (1/2)) :=
    (Gaussian.closedRectangle_isCompact _ _ _ _).isClosed.measurableSet
  have hclamp (x : bflatClosedRectangle) : bflatClamp x.1 = x := by
    apply Subtype.ext
    exact bflatClampVec_eq_self_of_closed x.2
  calc
    ∫ x : bflatClosedRectangle, f x * w x =
        ∫ x : bflatClosedRectangle, F x.1 := by
      apply integral_congr_ae
      filter_upwards with x
      simp [F, hclamp x]
    _ = ∫ x in Gaussian.closedRectangle (-1/2) (1/2) (-1/2) (1/2), F x := by
      rw [integral_subtype hclosed]
    _ = ∫ x in Gaussian.openRectangle (-1/2) (1/2) (-1/2) (1/2), F x := by
      rw [← Gaussian.rectangle_restrict_eq (-1/2) (1/2) (-1/2) (1/2)]
    _ = ∫ x : Vec 2 in bflatSquareObservationDomain, F x := by
      rw [← bflat_openSquare_eq_openRectangle]
    _ = _ := rfl

noncomputable def bflatModeDerivative (m n : ℕ) (i : Fin 2) (x : Vec 2) : ℝ :=
  cubeFreq bflatUnitSquare (Torus.natVec (bflatSquareModeIndex m n)) i *
    Torus.boxMode (cubeCorner bflatUnitSquare) (cubeScaleFactor bflatUnitSquare)
      (Finset.univ.erase i) (Torus.natVec (bflatSquareModeIndex m n)) x

private theorem bflatModeDerivative_continuous (m n : ℕ) (i : Fin 2) :
    Continuous (fun x : bflatClosedRectangle => bflatModeDerivative m n i x.1) := by
  exact (continuous_const.mul (Torus.continuous_boxMode _ _ _ _)).comp continuous_subtype_val

noncomputable def bflatModeObservationWeight (i : Fin 2) (m n : ℕ) :
    C(bflatClosedRectangle, ℝ) :=
  ⟨fun x =>
      (2 / Real.sqrt (cubeEig bflatUnitSquare
        (Torus.natVec (bflatSquareModeIndex m n)))) *
        (bflatModeDerivative m n 0 x.1 * bflatJEntry i 0 +
          bflatModeDerivative m n 1 x.1 * bflatJEntry i 1),
    by
      have h0 : Continuous (fun x : bflatClosedRectangle =>
          bflatModeDerivative m n 0 x.1 * bflatJEntry i 0) :=
        (bflatModeDerivative_continuous m n 0).mul continuous_const
      have h1 : Continuous (fun x : bflatClosedRectangle =>
          bflatModeDerivative m n 1 x.1 * bflatJEntry i 1) :=
        (bflatModeDerivative_continuous m n 1).mul continuous_const
      exact continuous_const.mul (h0.add h1)⟩

theorem bflatModeObservation_inner (i : Fin 2) (m n : ℕ)
    (f : C(bflatClosedRectangle, ℝ)) :
    inner ℝ (bflatSquareSineGradientUnit m n) (bflatSourceFieldClass i f) =
      bflatObservation (bflatModeObservationWeight i m n) f := by
  rw [bflatSquareSineGradientUnit, inner_smul_left]
  change (2 / Real.sqrt (cubeEig bflatUnitSquare
        (Torus.natVec (bflatSquareModeIndex m n)))) *
      inner ℝ
        (toHilbertVectorL2OfVecField
          (bflatSquareSineMode m n).toH1Function.grad_memVectorL2)
        (toHilbertVectorL2OfVecField (bflatSourceField_memL2 i f)) = _
  rw [inner_toHilbertVectorL2OfVecField_eq_integral]
  rw [bflatObservation_eq_openSquare_integral]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [bflatSquareSineMode_grad m n 0,
    bflatSquareSineMode_grad m n 1, ae_restrict_mem (isOpen_openCubeSet bflatUnitSquare).measurableSet]
    with x hgrad0 hgrad1 hx
  have hxClosed : x ∈ bflatClosedRectangle := by
    have h := bflatClampVec_mem x
    rw [bflatClampVec_eq_self_of_mem hx] at h
    exact h
  have hclamp : bflatClamp x = (⟨x, hxClosed⟩ : bflatClosedRectangle) := by
    apply Subtype.ext
    exact bflatClampVec_eq_self_of_mem hx
  fin_cases i <;>
    simp [bflatModeObservationWeight, bflatModeDerivative, bflatSourceField,
      bflatJEntry, vecDot, hclamp, hgrad0, hgrad1] <;> ring

end ASDExplicitGamma.Model
