module

public import ASDExplicitGamma.Model.BflatExactCaps
public import ASDExplicitGamma.Model.BflatModeTail
public import ASDExplicitGamma.Native.OldSignedFlatBoundaryEnergy
public import ASDExplicitGamma.Native.ParentBoundaryPlusMean
public import ASDExplicitGamma.Native.ParentBoundaryModelScales
public import ASDExplicitGamma.Gaussian.SupMeanShellUnitSupremum
public import ASDExplicitGamma.Gaussian.Q3WeightedBandSpatial
public import Homogenization.Deterministic.ConstantCoefficientDirichletBesov.CenteredCubeScaleTransport
public import Algsuperdiff.Section3.Provider.Orlicz.TwoTermCalculus
public import ASDExplicitGamma.Main.AffineFlatBoundary

import Mathlib.Tactic

/-! All-observer companion of the flat-boundary cap (the private argument, re-derived, without the unused observer bound). -/

@[expose] public section

open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model ASDExplicitGamma.Native
open ASDExplicitGamma.Triadic ASDExplicitGamma.Response
open ASDExplicitGamma.Scalar
open Homogenization MeasureTheory
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped Pointwise

namespace ASDExplicitGamma.Main

noncomputable section

private theorem main_affine_flat_boundary_observation_covariance
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (d : ℕ → H) (hD : Summable (fun n => ‖d n‖ ^ 2))
    (T : H →L[ℝ] C(bflatClosedRectangle, ℝ)) (C : ℝ) (hC : 0 ≤ C)
    (hT : ∀ n, ‖T (d n)‖ ≤ C * ‖d n‖)
    (w z : C(bflatClosedRectangle, ℝ)) (K : bflatClosedRectangle →
      bflatClosedRectangle → ℝ)
    (hcov : ∀ x y, (∑' n : ℕ, T (d n) x * T (d n) y) = K x y) :
    (∑' n : ℕ, bflatObservation w (T (d n)) *
      bflatObservation z (T (d n))) =
      ∫ p : bflatClosedRectangle × bflatClosedRectangle,
        K p.1 p.2 * w p.1 * z p.2
        ∂((volume : Measure bflatClosedRectangle).prod volume) := by
  let F (n : ℕ) (p : bflatClosedRectangle × bflatClosedRectangle) : ℝ :=
    (T (d n) p.1 * w p.1) * (T (d n) p.2 * z p.2)
  let μ₂ : Measure (bflatClosedRectangle × bflatClosedRectangle) :=
    (volume : Measure bflatClosedRectangle).prod volume
  have hFcont (n : ℕ) : Continuous (F n) := by
    change Continuous (fun p : bflatClosedRectangle × bflatClosedRectangle =>
      (T (d n) p.1 * w p.1) * (T (d n) p.2 * z p.2))
    fun_prop
  have hFint (n : ℕ) : Integrable (F n) μ₂ :=
    (hFcont n).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hFbound (n : ℕ) (p : bflatClosedRectangle × bflatClosedRectangle) :
      ‖F n p‖ ≤ (C ^ 2 * ‖w‖ * ‖z‖) * ‖d n‖ ^ 2 := by
    dsimp [F]
    rw [abs_mul, abs_mul, abs_mul]
    have hfx : |T (d n) p.1| ≤ C * ‖d n‖ := by
      calc
        |T (d n) p.1| = ‖T (d n) p.1‖ := by rw [Real.norm_eq_abs]
        _ ≤ ‖T (d n)‖ := ContinuousMap.norm_coe_le_norm _ _
        _ ≤ C * ‖d n‖ := hT n
    have hfy : |T (d n) p.2| ≤ C * ‖d n‖ := by
      calc
        |T (d n) p.2| = ‖T (d n) p.2‖ := by rw [Real.norm_eq_abs]
        _ ≤ ‖T (d n)‖ := ContinuousMap.norm_coe_le_norm _ _
        _ ≤ C * ‖d n‖ := hT n
    have hw : |w p.1| ≤ ‖w‖ := by
      calc
        |w p.1| = ‖w p.1‖ := by rw [Real.norm_eq_abs]
        _ ≤ ‖w‖ := ContinuousMap.norm_coe_le_norm _ _
    have hz : |z p.2| ≤ ‖z‖ := by
      calc
        |z p.2| = ‖z p.2‖ := by rw [Real.norm_eq_abs]
        _ ≤ ‖z‖ := ContinuousMap.norm_coe_le_norm _ _
    have hn : 0 ≤ C * ‖d n‖ := mul_nonneg hC (norm_nonneg _)
    have hleft := mul_le_mul hfx hw (abs_nonneg _) hn
    have hright := mul_le_mul hfy hz (abs_nonneg _) hn
    calc
      |T (d n) p.1| * |w p.1| *
          (|T (d n) p.2| * |z p.2|) =
        (|T (d n) p.1| * |w p.1|) *
          (|T (d n) p.2| * |z p.2|) := by ring
      _ ≤ ((C * ‖d n‖) * ‖w‖) * ((C * ‖d n‖) * ‖z‖) :=
        mul_le_mul hleft hright
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
          (mul_nonneg hn (norm_nonneg _))
      _ = (C ^ 2 * ‖w‖ * ‖z‖) * ‖d n‖ ^ 2 := by ring
  have hFsum : Summable (fun n : ℕ => ∫ p, ‖F n p‖ ∂μ₂) := by
    apply Summable.of_nonneg_of_le
      (fun n => integral_nonneg fun p => norm_nonneg (F n p))
      (fun n => ?_)
      (hD.mul_left ((μ₂.real Set.univ) * (C ^ 2 * ‖w‖ * ‖z‖)))
    calc
      ∫ p, ‖F n p‖ ∂μ₂ ≤
          ∫ p, (C ^ 2 * ‖w‖ * ‖z‖) * ‖d n‖ ^ 2 ∂μ₂ := by
        apply integral_mono (hFint n).norm (integrable_const _)
        intro p
        exact hFbound n p
      _ = (μ₂.real Set.univ) * ((C ^ 2 * ‖w‖ * ‖z‖) * ‖d n‖ ^ 2) := by
        rw [integral_const, smul_eq_mul]
      _ = (μ₂.real Set.univ) * (C ^ 2 * ‖w‖ * ‖z‖) * ‖d n‖ ^ 2 := by ring
  have hsumint := integral_tsum_of_summable_integral_norm hFint hFsum
  have hpoint (p : bflatClosedRectangle × bflatClosedRectangle) :
      (∑' n : ℕ, F n p) = K p.1 p.2 * w p.1 * z p.2 := by
    change (∑' n : ℕ,
      (T (d n) p.1 * w p.1) * (T (d n) p.2 * z p.2)) = _
    calc
      _ = (∑' n : ℕ, T (d n) p.1 * T (d n) p.2) *
          (w p.1 * z p.2) := by
        rw [← tsum_mul_right]
        apply tsum_congr
        intro n
        ring
      _ = _ := by rw [hcov p.1 p.2]; ring
  calc
    _ = ∑' n : ℕ, ∫ p, F n p ∂μ₂ := by
      apply tsum_congr
      intro n
      change bflatObservation w (T (d n)) *
          bflatObservation z (T (d n)) = _
      rw [bflatObservation_apply, bflatObservation_apply]
      symm
      exact integral_prod_mul
        (fun x => T (d n) x * w x) (fun y => T (d n) y * z y)
    _ = ∫ p, ∑' n : ℕ, F n p ∂μ₂ := hsumint
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with p
      exact hpoint p

private theorem main_affine_flat_boundary_setIntegral_dilation
    (m : ℤ) (F : Vec 2 → ℝ) :
    ∫ x in openCubeSet (originCube 2 m),
        F ((centeredCubeScale m)⁻¹ • x) ∂volume =
      (centeredCubeScale m)^2 *
        ∫ x in openCubeSet (originCube 2 0), F x ∂volume := by
  have hchange := Measure.setIntegral_comp_smul_of_pos
    (μ := volume) (f := fun x => F ((centeredCubeScale m)⁻¹ • x))
    (s := openCubeSet (originCube 2 0)) (centeredCubeScale_pos m)
  rw [← Homogenization.centeredOpenCube_eq_smul_unitCenteredOpenCube (d := 2) m]
    at hchange
  have hcancel (x : Vec 2) :
      (centeredCubeScale m)⁻¹ • (centeredCubeScale m • x) = x := by
    rw [smul_smul, inv_mul_cancel₀ (centeredCubeScale_ne_zero m), one_smul]
  have hchange' :
      ∫ x in openCubeSet (originCube 2 0), F x ∂volume =
        ((centeredCubeScale m)^2)⁻¹ *
          ∫ x in openCubeSet (originCube 2 m),
            F ((centeredCubeScale m)⁻¹ • x) ∂volume := by
    simpa only [smul_smul, inv_mul_cancel₀ (centeredCubeScale_ne_zero m),
      one_smul, Module.finrank_fin_fun, smul_eq_mul] using hchange
  calc
    _ = (centeredCubeScale m)^2 *
          (((centeredCubeScale m)^2)⁻¹ *
            ∫ x in openCubeSet (originCube 2 m),
              F ((centeredCubeScale m)⁻¹ • x) ∂volume) := by
        rw [← mul_assoc, mul_inv_cancel₀
          (pow_ne_zero 2 (centeredCubeScale_ne_zero m)), one_mul]
    _ = _ := by rw [hchange']

private theorem main_affine_flat_boundary_unit_eq_inv_smul_cube
    {d : ℕ} (m : ℤ) :
    openCubeSet (originCube d 0) =
      (centeredCubeScale m)⁻¹ • openCubeSet (originCube d m) := by
  rw [Homogenization.openCubeSet_originCube_eq_smul_originCube_zero (d := d) m]
  rw [show cubeScaleFactor (originCube d m) = centeredCubeScale m by rfl]
  rw [smul_smul, inv_mul_cancel₀ (centeredCubeScale_ne_zero m), one_smul]

private theorem main_affine_flat_boundary_unit_domain :
    openCubeSet (originCube 2 0) = openCubeSet bflatUnitSquare := by
  ext x
  simp [bflatUnitSquare, Homogenization.openCubeSet, originCube,
    Homogenization.cubeScaleFactor]

private theorem main_affine_flat_boundary_model_eq_inv_smul_cube
    (m : ℤ) :
    openCubeSet bflatUnitSquare =
      (centeredCubeScale m)⁻¹ • openCubeSet (originCube 2 m) := by
  calc
    openCubeSet bflatUnitSquare = openCubeSet (originCube 2 0) :=
      main_affine_flat_boundary_unit_domain.symm
    _ = (centeredCubeScale m)⁻¹ • openCubeSet (originCube 2 m) :=
      main_affine_flat_boundary_unit_eq_inv_smul_cube m

private theorem mainAffineFlatBoundaryCast_grad
    {d : ℕ} {U V : Set (Vec d)} (hUV : U = V)
    (φ : H10Function U) (x : Vec d) :
    (hUV ▸ φ).toH1Function.grad x = φ.toH1Function.grad x := by
  subst V
  rfl

private noncomputable def mainAffineFlatBoundaryTestPushforward
    {m : ℤ}
    (φ : H10Function (openCubeSet bflatUnitSquare)) :
    H10Function (openCubeSet (originCube 2 m)) :=
  centeredCubeScale m • H10Function.unscale
    (inv_pos.mpr (centeredCubeScale_pos m))
    (main_affine_flat_boundary_model_eq_inv_smul_cube m ▸ φ)

private theorem mainAffineFlatBoundaryTestPushforward_grad
    {m : ℤ}
    (φ : H10Function (openCubeSet bflatUnitSquare)) (x : Vec 2) :
    (mainAffineFlatBoundaryTestPushforward (m := m) φ).toH1Function.grad x =
      φ.toH1Function.grad ((centeredCubeScale m)⁻¹ • x) := by
  unfold mainAffineFlatBoundaryTestPushforward
  change centeredCubeScale m •
      (H10Function.unscale (inv_pos.mpr (centeredCubeScale_pos m))
        (main_affine_flat_boundary_model_eq_inv_smul_cube m ▸ φ)).toH1Function.grad x = _
  rw [H10Function.unscale_toH1Function, H1Function.unscale_grad]
  rw [mainAffineFlatBoundaryCast_grad]
  ext i
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp [centeredCubeScale_ne_zero m]

private noncomputable def mainAffineFlatBoundaryTestPotential
    (m : ℤ) (a b : ℕ) : H10Function (openCubeSet (originCube 2 m)) :=
  ((centeredCubeScale m)⁻¹ *
      (2 / Real.sqrt (cubeEig bflatUnitSquare
        (Torus.natVec (bflatSquareModeIndex a b))))) •
    mainAffineFlatBoundaryTestPushforward
      (m := m) (bflatSquareSineMode a b)

private noncomputable def mainAffineFlatBoundaryTestGradient
    (m : ℤ) (a b : ℕ) : HilbertVectorL2 (openCubeSet (originCube 2 m)) :=
  (mainAffineFlatBoundaryTestPotential m a b).toH1Function.gradToHilbertVectorL2

private noncomputable def bflatSquareSineGradientUnitField (a b : ℕ) :
    Vec 2 → Vec 2 :=
  fun x => (2 / Real.sqrt (cubeEig bflatUnitSquare
      (Torus.natVec (bflatSquareModeIndex a b)))) •
    (bflatSquareSineMode a b).toH1Function.grad x

private theorem mainAffineFlatBoundaryTestPotential_grad
    (m : ℤ) (a b : ℕ) (x : Vec 2) :
    (mainAffineFlatBoundaryTestPotential m a b).grad x =
      (centeredCubeScale m)⁻¹ •
        bflatSquareSineGradientUnitField a b
          ((centeredCubeScale m)⁻¹ • x) := by
  -- The field abbreviation below unfolds to the normalized unit-square sine gradient.
  change ((((centeredCubeScale m)⁻¹ *
      (2 / Real.sqrt (cubeEig bflatUnitSquare
        (Torus.natVec (bflatSquareModeIndex a b))))) •
      (mainAffineFlatBoundaryTestPushforward (m := m)
        (bflatSquareSineMode a b)).toH1Function).grad x) = _
  simp only [H1Function.smul_grad]
  rw [mainAffineFlatBoundaryTestPushforward_grad]
  simp only [bflatSquareSineGradientUnitField, Pi.smul_apply, smul_eq_mul]
  rw [← smul_smul]

private theorem mainAffineFlatBoundaryTestGradient_inner
    (m : ℤ) (a b c d : ℕ) :
    inner ℝ (mainAffineFlatBoundaryTestGradient m a b)
        (mainAffineFlatBoundaryTestGradient m c d) =
      inner ℝ (bflatSquareSineGradientUnit a b)
        (bflatSquareSineGradientUnit c d) := by
  let R := centeredCubeScale m
  have hmem₁ := (mainAffineFlatBoundaryTestPotential m a b).toH1Function.grad_memVectorL2
  have hmem₂ := (mainAffineFlatBoundaryTestPotential m c d).toH1Function.grad_memVectorL2
  change inner ℝ (toHilbertVectorL2OfVecField hmem₁)
      (toHilbertVectorL2OfVecField hmem₂) = _
  rw [inner_toHilbertVectorL2OfVecField_eq_integral hmem₁ hmem₂]
  have hpoint₁ (x : Vec 2) := mainAffineFlatBoundaryTestPotential_grad m a b x
  have hpoint₂ (x : Vec 2) := mainAffineFlatBoundaryTestPotential_grad m c d x
  have hformula :
      ∫ x in openCubeSet (originCube 2 m),
        vecDot ((mainAffineFlatBoundaryTestPotential m a b).grad x)
          ((mainAffineFlatBoundaryTestPotential m c d).grad x) ∂volume =
      ∫ x in openCubeSet (originCube 2 m),
        vecDot ((centeredCubeScale m)⁻¹ •
            bflatSquareSineGradientUnitField a b
              ((centeredCubeScale m)⁻¹ • x))
          ((centeredCubeScale m)⁻¹ •
            bflatSquareSineGradientUnitField c d
              ((centeredCubeScale m)⁻¹ • x)) ∂volume := by
    apply integral_congr_ae
    filter_upwards [] with x
    rw [hpoint₁ x, hpoint₂ x]
  have hmodel :
      inner ℝ (bflatSquareSineGradientUnit a b)
          (bflatSquareSineGradientUnit c d) =
        ∫ x in openCubeSet (originCube 2 0),
          vecDot (bflatSquareSineGradientUnitField a b x)
            (bflatSquareSineGradientUnitField c d x) ∂volume := by
    rw [bflatSquareSineGradientUnit, bflatSquareSineGradientUnit,
      inner_smul_left, inner_smul_right,
      bflatSquareSineModeHilbertGradient, bflatSquareSineModeHilbertGradient,
      inner_toHilbertVectorL2OfVecField_eq_integral]
    simp only [bflatSquareSineGradientUnitField,
      vecDot_smul_left, vecDot_smul_right]
    simp only [starRingEnd_apply]
    ring_nf
    rw [integral_mul_const, integral_const_mul]
    have hdom : openCubeSet bflatUnitSquare =ᵐ[volume]
        openCubeSet (originCube 2 0) := by
      filter_upwards [] with x
      exact congrArg (fun U : Set (Vec 2) => x ∈ U)
        main_affine_flat_boundary_unit_domain.symm
    rw [setIntegral_congr_set hdom]
    simp only [star_trivial]
    ring_nf
  rw [hformula, hmodel]
  simp only [vecDot_smul_left, vecDot_smul_right]
  rw [integral_const_mul, integral_const_mul]
  rw [main_affine_flat_boundary_setIntegral_dilation m
    (fun y => vecDot (bflatSquareSineGradientUnitField a b y)
      (bflatSquareSineGradientUnitField c d y))]
  field_simp [centeredCubeScale_ne_zero m]

private theorem mainAffineFlatBoundaryTestGradient_orthonormal (m : ℤ) :
    Orthonormal ℝ (fun p : ℕ × ℕ =>
      mainAffineFlatBoundaryTestGradient m p.1 p.2) := by
  rw [orthonormal_iff_ite]
  intro p q
  rcases p with ⟨a, b⟩
  rcases q with ⟨c, d⟩
  rw [mainAffineFlatBoundaryTestGradient_inner]
  simpa only [Prod.mk.injEq] using bflatSquareSineGradientUnit_inner a b c d

private theorem mainAffineFlatBoundaryTestGradient_mem
    (m : ℤ) (a b : ℕ) :
    mainAffineFlatBoundaryTestGradient m a b ∈
      (lambda8H10GradientRange
        (isOpenBoundedConvexDomain_openCubeSet (originCube 2 m))).toSubmodule := by
  exact parent_boundary_h10_gradient_mem m
    (mainAffineFlatBoundaryTestPotential m a b)

private theorem mainAffineFlatBoundary_finite_bessel
    (m : ℤ) (b : ℝ) (L : {l : ℝ // 0 < l}) (v : Vec 2)
    (w : WhiteNoise) (N : ℕ) :
    (∑ p ∈ Finset.range N ×ˢ Finset.range N,
      (inner ℝ (mainAffineFlatBoundaryTestGradient m p.1 p.2)
        (parentBoundaryRawLoadOperator (originCube 2 m) b L v
          w)) ^ 2) ≤
      ‖parentBoundaryDirichletLoadOperator (originCube 2 m) b L v
        w‖ ^ 2 := by
  let V := (lambda8H10GradientRange
    (isOpenBoundedConvexDomain_openCubeSet (originCube 2 m))).toSubmodule
  let e : ℕ × ℕ → HilbertVectorL2 (openCubeSet (originCube 2 m)) :=
    fun p => mainAffineFlatBoundaryTestGradient m p.1 p.2
  have he : Orthonormal ℝ e := by
    simpa only [e] using mainAffineFlatBoundaryTestGradient_orthonormal m
  have hmem (p : ℕ × ℕ) (hp : p ∈ Finset.range N ×ˢ Finset.range N) :
      e p ∈ V := by
    exact mainAffineFlatBoundaryTestGradient_mem m p.1 p.2
  have h := bflat_projection_finite_bessel V e he
    (Finset.range N ×ˢ Finset.range N) hmem
    (parentBoundaryRawLoadOperator (originCube 2 m) b L v
      w)
  simpa only [V, e, parentBoundaryDirichletLoadOperator,
    ContinuousLinearMap.comp_apply] using h

private noncomputable def mainAffineFlatBoundaryScaleMap
    (R : {r : ℝ // 0 < r}) :
    C(bflatClosedRectangle,
      closedRectangle (-R.1 / 2) (R.1 / 2) (-R.1 / 2) (R.1 / 2)) := by
  refine ⟨fun x => ⟨R.1 • x.1, ?_⟩, ?_⟩
  · have hx : x.1 0 ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2) ∧
        x.1 1 ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2) := by
      simpa [bflatClosedRectangle, Gaussian.closedRectangle] using x.2
    constructor
    · constructor
      · calc
          -R.1 / 2 = R.1 * (-1 / 2) := by ring
          _ ≤ R.1 * x.1 0 := mul_le_mul_of_nonneg_left hx.1.1 R.2.le
      · calc
          R.1 * x.1 0 ≤ R.1 * (1 / 2) := mul_le_mul_of_nonneg_left hx.1.2 R.2.le
          _ = R.1 / 2 := by ring
    · constructor
      · calc
          -R.1 / 2 = R.1 * (-1 / 2) := by ring
          _ ≤ R.1 * x.1 1 := mul_le_mul_of_nonneg_left hx.2.1 R.2.le
      · calc
          R.1 * x.1 1 ≤ R.1 * (1 / 2) := mul_le_mul_of_nonneg_left hx.2.2 R.2.le
          _ = R.1 / 2 := by ring
  · exact Continuous.subtype_mk
      ((continuous_const_smul R.1).comp continuous_subtype_val) _

private noncomputable def mainAffineFlatBoundaryPullback
    (R : {r : ℝ // 0 < r}) (b : ℝ) (L : {l : ℝ // 0 < l}) :
    Gaussian.Q3H3Range (-R.1 / 2) (R.1 / 2) (-R.1 / 2) (R.1 / 2) b L →L[ℝ]
      C(bflatClosedRectangle, ℝ) :=
  (ContinuousMap.compCLM ℝ ℝ (mainAffineFlatBoundaryScaleMap R)).comp
    (Gaussian.q3H3RangeValue (-R.1 / 2) (R.1 / 2) (-R.1 / 2) (R.1 / 2) b L)

private theorem mainAffineFlatBoundaryPullback_norm_le
    (R : {r : ℝ // 0 < r}) (b : ℝ) (L : {l : ℝ // 0 < l})
    (u : Gaussian.Q3H3Range (-R.1 / 2) (R.1 / 2)
      (-R.1 / 2) (R.1 / 2) b L) :
    ‖mainAffineFlatBoundaryPullback R b L u‖ ≤
      Gaussian.rectangleSobolevConstant (-R.1 / 2) (R.1 / 2)
        (-R.1 / 2) (R.1 / 2) * ‖u‖ := by
  let r := mainAffineFlatBoundaryScaleMap R
  change ‖(Gaussian.q3H3RangeValue (-R.1 / 2) (R.1 / 2)
    (-R.1 / 2) (R.1 / 2) b L u).comp r‖ ≤ _
  have hC : 0 ≤ Gaussian.rectangleSobolevConstant (-R.1 / 2) (R.1 / 2)
      (-R.1 / 2) (R.1 / 2) := by
    dsimp [Gaussian.rectangleSobolevConstant]
    exact Real.sqrt_nonneg _
  apply (ContinuousMap.norm_le _
    (mul_nonneg hC (norm_nonneg _))).2
  intro x
  exact ((Gaussian.q3H3RangeValue (-R.1 / 2) (R.1 / 2)
    (-R.1 / 2) (R.1 / 2) b L u).norm_coe_le_norm (r x)).trans <| by
    change ‖(Gaussian.q3H3RangeC1 (-R.1 / 2) (R.1 / 2)
      (-R.1 / 2) (R.1 / 2) b L u) 0‖ ≤ _
    exact (norm_le_pi_norm _ 0).trans
      (Gaussian.q3H3RangeC1_norm_le (-R.1 / 2) (R.1 / 2)
        (-R.1 / 2) (R.1 / 2) b (by linarith [R.2]) (by linarith [R.2]) L u)

private theorem mainAffineFlatBoundaryScaleMap_coord
    (R : {r : ℝ // 0 < r}) (x : bflatClosedRectangle) (k : Fin 2) :
    (mainAffineFlatBoundaryScaleMap R x).1 k = R.1 * x.1 k := by
  rfl

private theorem main_affine_flat_boundary_scale_ratio
    (R : {r : ℝ // 0 < r}) (L : {l : ℝ // 0 < l})
    (x y : bflatClosedRectangle) (k : Fin 2) :
    (((R.1 * x.1 k) - (R.1 * y.1 k)) / L.1) =
      (x.1 k - y.1 k) / (L.1 / R.1) := by
  field_simp [ne_of_gt R.2, ne_of_gt L.2]

private theorem main_affine_flat_boundary_pullback_covariance
    {ι : Type*} [Countable ι]
    (e : HilbertBasis ι ℝ WhiteNoise) (R : {r : ℝ // 0 < r})
    (b : ℝ) (L : {l : ℝ // 0 < l}) (d : ℕ)
    (hratio : L.1 / R.1 =
      (ASDExplicitGamma.Numerics.Model.q3ModeLength d : ℝ))
    (x y : bflatClosedRectangle) :
    (∑' n : ℕ,
      mainAffineFlatBoundaryPullback R b L
        (Gaussian.q3H3Directions (-R.1 / 2) (R.1 / 2)
          (-R.1 / 2) (R.1 / 2) b L e n) x *
      mainAffineFlatBoundaryPullback R b L
        (Gaussian.q3H3Directions (-R.1 / 2) (R.1 / 2)
          (-R.1 / 2) (R.1 / 2) b L e n) y) =
        b ^ 2 * ASDExplicitGamma.q3Cov ((x.1 0 - y.1 0) /
          (ASDExplicitGamma.Numerics.Model.q3ModeLength d : ℝ)) *
          ASDExplicitGamma.q3Cov ((x.1 1 - y.1 1) /
          (ASDExplicitGamma.Numerics.Model.q3ModeLength d : ℝ)) := by
  let r := mainAffineFlatBoundaryScaleMap R
  have hc := Gaussian.q3H3Directions_covariance (-R.1 / 2) (R.1 / 2)
    (-R.1 / 2) (R.1 / 2) b (by linarith [R.2]) (by linarith [R.2]) L e (r x) (r y)
  have hval (n : ℕ) (z : bflatClosedRectangle) :
      mainAffineFlatBoundaryPullback R b L
        (Gaussian.q3H3Directions (-R.1 / 2) (R.1 / 2)
          (-R.1 / 2) (R.1 / 2) b L e n) z =
      Gaussian.q3H3RangeValue (-R.1 / 2) (R.1 / 2)
        (-R.1 / 2) (R.1 / 2) b L
          (Gaussian.q3H3Directions (-R.1 / 2) (R.1 / 2)
            (-R.1 / 2) (R.1 / 2) b L e n) (r z) := by
    rfl
  calc
    _ = ∑' n : ℕ,
        Gaussian.q3H3RangeValue (-R.1 / 2) (R.1 / 2)
          (-R.1 / 2) (R.1 / 2) b L
            (Gaussian.q3H3Directions (-R.1 / 2) (R.1 / 2)
              (-R.1 / 2) (R.1 / 2) b L e n) (r x) *
        Gaussian.q3H3RangeValue (-R.1 / 2) (R.1 / 2)
          (-R.1 / 2) (R.1 / 2) b L
            (Gaussian.q3H3Directions (-R.1 / 2) (R.1 / 2)
              (-R.1 / 2) (R.1 / 2) b L e n) (r y) := by
      apply tsum_congr
      intro n
      rw [hval, hval]
    _ = b ^ 2 * ASDExplicitGamma.q3Cov
        (((r x).1 0 - (r y).1 0) / L.1) *
        ASDExplicitGamma.q3Cov (((r x).1 1 - (r y).1 1) / L.1) := hc
    _ = _ := by
      rw [mainAffineFlatBoundaryScaleMap_coord,
        mainAffineFlatBoundaryScaleMap_coord,
        mainAffineFlatBoundaryScaleMap_coord,
        mainAffineFlatBoundaryScaleMap_coord,
        main_affine_flat_boundary_scale_ratio,
        main_affine_flat_boundary_scale_ratio, hratio]

private theorem main_affine_flat_boundary_scaled_observation_covariance
    {ι : Type*} [Countable ι]
    (e : HilbertBasis ι ℝ WhiteNoise) (R : {r : ℝ // 0 < r})
    (b : ℝ) (L : {l : ℝ // 0 < l}) (d : ℕ)
    (hratio : L.1 / R.1 =
      (ASDExplicitGamma.Numerics.Model.q3ModeLength d : ℝ))
    (hD : Summable (fun n : ℕ =>
      ‖Gaussian.q3H3Directions (-R.1 / 2) (R.1 / 2)
        (-R.1 / 2) (R.1 / 2) b L e n‖ ^ 2))
    (hT : ∀ n : ℕ, ‖mainAffineFlatBoundaryPullback R b L
      (Gaussian.q3H3Directions (-R.1 / 2) (R.1 / 2)
        (-R.1 / 2) (R.1 / 2) b L e n)‖ ≤
      Gaussian.rectangleSobolevConstant (-R.1 / 2) (R.1 / 2)
        (-R.1 / 2) (R.1 / 2) *
      ‖Gaussian.q3H3Directions (-R.1 / 2) (R.1 / 2)
        (-R.1 / 2) (R.1 / 2) b L e n‖)
    (i : Fin 2) (a c : ℕ) :
    (∑' n : ℕ,
      bflatObservation (bflatModeObservationWeight i a c)
        (mainAffineFlatBoundaryPullback R b L
          (Gaussian.q3H3Directions (-R.1 / 2) (R.1 / 2)
            (-R.1 / 2) (R.1 / 2) b L e n)) ^ 2) =
      ∫ p : bflatClosedRectangle × bflatClosedRectangle,
        (b ^ 2 * ASDExplicitGamma.q3Cov
          ((p.1.1 0 - p.2.1 0) /
            (ASDExplicitGamma.Numerics.Model.q3ModeLength d : ℝ)) *
          ASDExplicitGamma.q3Cov ((p.1.1 1 - p.2.1 1) /
            (ASDExplicitGamma.Numerics.Model.q3ModeLength d : ℝ))) *
          bflatModeObservationWeight i a c p.1 *
          bflatModeObservationWeight i a c p.2
        ∂((volume : Measure bflatClosedRectangle).prod volume) := by
  let T := mainAffineFlatBoundaryPullback R b L
  let v := Gaussian.q3H3Directions (-R.1 / 2) (R.1 / 2)
    (-R.1 / 2) (R.1 / 2) b L e
  have hv : Summable (fun n : ℕ => ‖v n‖ ^ 2) := by simpa only [v] using hD
  let C : ℝ := Gaussian.rectangleSobolevConstant
    (-R.1 / 2) (R.1 / 2) (-R.1 / 2) (R.1 / 2)
  have hC : 0 ≤ C := by
    dsimp [C, Gaussian.rectangleSobolevConstant]
    exact Real.sqrt_nonneg _
  have hT (n : ℕ) : ‖T (v n)‖ ≤ C * ‖v n‖ := by
    simpa only [T, C, v] using hT n
  let K : bflatClosedRectangle → bflatClosedRectangle → ℝ := fun x y =>
    b ^ 2 * ASDExplicitGamma.q3Cov
      ((x.1 0 - y.1 0) /
        (ASDExplicitGamma.Numerics.Model.q3ModeLength d : ℝ)) *
      ASDExplicitGamma.q3Cov ((x.1 1 - y.1 1) /
        (ASDExplicitGamma.Numerics.Model.q3ModeLength d : ℝ))
  have hcov : ∀ x y, (∑' n : ℕ, T (v n) x * T (v n) y) = K x y := by
    intro x y
    simpa only [K] using
      main_affine_flat_boundary_pullback_covariance e R b L d hratio x y
  let H := Gaussian.Q3H3Range (-R.1 / 2) (R.1 / 2)
    (-R.1 / 2) (R.1 / 2) b L
  letI : InnerProductSpace ℝ H := Gaussian.instQ3H3RangeInnerProductSpace
    (-R.1 / 2) (R.1 / 2) (-R.1 / 2) (R.1 / 2) b L
  calc
    _ = ∑' n : ℕ,
        bflatObservation (bflatModeObservationWeight i a c) (T (v n)) *
          bflatObservation (bflatModeObservationWeight i a c) (T (v n)) := by
      apply tsum_congr
      intro n
      ring
    _ = ∫ p : bflatClosedRectangle × bflatClosedRectangle,
        K p.1 p.2 * bflatModeObservationWeight i a c p.1 *
          bflatModeObservationWeight i a c p.2
        ∂((volume : Measure bflatClosedRectangle).prod volume) :=
      @main_affine_flat_boundary_observation_covariance H
        inferInstance inferInstance inferInstance v hv T C hC hT
        (bflatModeObservationWeight i a c) (bflatModeObservationWeight i a c) K hcov
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with p
      simp only [K]

private theorem main_affine_flat_boundary_scaled_observation_integral
    {ι : Type*} [Countable ι]
    (e : HilbertBasis ι ℝ WhiteNoise) (R : {r : ℝ // 0 < r})
    (b : ℝ) (L : {l : ℝ // 0 < l}) (d : ℕ)
    (hratio : L.1 / R.1 =
      (ASDExplicitGamma.Numerics.Model.q3ModeLength d : ℝ))
    (i : Fin 2) (a c : ℕ) :
    (∑' n : ℕ,
      bflatObservation (bflatModeObservationWeight i a c)
        (mainAffineFlatBoundaryPullback R b L
          (Gaussian.q3H3Directions (-R.1 / 2) (R.1 / 2)
            (-R.1 / 2) (R.1 / 2) b L e n)) ^ 2) =
      ∫ p : bflatClosedRectangle × bflatClosedRectangle,
        (b ^ 2 * ASDExplicitGamma.q3Cov
          ((p.1.1 0 - p.2.1 0) /
            (ASDExplicitGamma.Numerics.Model.q3ModeLength d : ℝ)) *
          ASDExplicitGamma.q3Cov ((p.1.1 1 - p.2.1 1) /
            (ASDExplicitGamma.Numerics.Model.q3ModeLength d : ℝ))) *
          bflatModeObservationWeight i a c p.1 *
          bflatModeObservationWeight i a c p.2
        ∂((volume : Measure bflatClosedRectangle).prod volume) := by
  have hD := Gaussian.q3H3Directions_summable (-R.1 / 2) (R.1 / 2)
    (-R.1 / 2) (R.1 / 2) b L e
  have hT (n : ℕ) := mainAffineFlatBoundaryPullback_norm_le R b L
    (Gaussian.q3H3Directions (-R.1 / 2) (R.1 / 2)
      (-R.1 / 2) (R.1 / 2) b L e n)
  exact main_affine_flat_boundary_scaled_observation_covariance
    e R b L d hratio hD hT i a c

private theorem main_affine_flat_boundary_scale_covariance
    {ι : Type*} [Countable ι]
    (e : HilbertBasis ι ℝ WhiteNoise) (R : {r : ℝ // 0 < r})
    (b : ℝ) (L : {l : ℝ // 0 < l}) (d : ℕ)
    (hratio : L.1 / R.1 =
      (ASDExplicitGamma.Numerics.Model.q3ModeLength d : ℝ))
    (i : Fin 2) (a c : ℕ) :
    (∑' n : ℕ,
      bflatObservation (bflatModeObservationWeight i a c)
        (mainAffineFlatBoundaryPullback R b L
          (Gaussian.q3H3Directions (-R.1 / 2) (R.1 / 2)
            (-R.1 / 2) (R.1 / 2) b L e n)) ^ 2) =
      bflatModeSeriesVariance e i a c b (bflatQ3ModeScale d) := by
  rw [main_affine_flat_boundary_scaled_observation_integral e R b L d
    hratio i a c, bflatModeSeriesVariance_eq_covariance_integral]
  apply integral_congr_ae
  filter_upwards [] with p
  simp only [bflatQ3ModeScale]

private theorem main_affine_flat_boundary_unit_observation
    (i : Fin 2) (a c : ℕ) (f : C(bflatClosedRectangle, ℝ)) :
    (∫ x in openCubeSet bflatUnitSquare,
      vecDot (bflatSquareSineGradientUnitField a c x)
        (f (bflatClamp x) • mainFlatRotatedBasis i) ∂volume) =
      bflatObservation (bflatModeObservationWeight i a c) f := by
  let hgrad := (bflatSquareSineMode a c).toH1Function.grad_memVectorL2
  let s := 2 / Real.sqrt (cubeEig bflatUnitSquare
    (Torus.natVec (bflatSquareModeIndex a c)))
  let hunit := hgrad.const_smul s
  have hunit_eq : toHilbertVectorL2OfVecField hunit =
      bflatSquareSineGradientUnit a c := by
    rw [bflatSquareSineGradientUnit, bflatSquareSineModeHilbertGradient]
    change toHilbertVectorL2 (memHilbertVectorL2_hilbertifyVecField hunit) =
      s • toHilbertVectorL2 (memHilbertVectorL2_hilbertifyVecField hgrad)
    exact MeasureTheory.MemLp.toLp_const_smul s
      (memHilbertVectorL2_hilbertifyVecField hgrad)
  have hsource : MemVectorL2 bflatSquareObservationDomain
      (bflatSourceField i f) := bflatSourceField_memL2 i f
  have hsource_eq : toHilbertVectorL2OfVecField hsource =
      bflatSourceFieldClass i f := by rfl
  have hinner := inner_toHilbertVectorL2OfVecField_eq_integral hunit hsource
  have hobs := bflatModeObservation_inner i a c f
  rw [← hunit_eq, ← hsource_eq, hinner] at hobs
  have hrot : mainFlatRotatedBasis i = fun k => bflatJEntry i k := by
    fin_cases i <;> ext k <;> fin_cases k <;>
      simp [mainFlatRotatedBasis, responsePlanarJ, matVecMul,
        basisVec, bflatJEntry, Pi.single_apply, Fin.sum_univ_two]
  calc
    _ = ∫ x in openCubeSet bflatUnitSquare,
        vecDot (bflatSquareSineGradientUnitField a c x)
          (bflatSourceField i f x) ∂volume := by
      apply integral_congr_ae
      filter_upwards [] with x
      change vecDot (bflatSquareSineGradientUnitField a c x)
          (f (bflatClamp x) • mainFlatRotatedBasis i) =
        vecDot (bflatSquareSineGradientUnitField a c x)
          (fun k => f (bflatClamp x) * bflatJEntry i k)
      rw [hrot]
      rfl
    _ = _ := hobs

private theorem main_affine_flat_boundary_pairing_dilation
    (m : ℤ) (b : ℝ) (L : {l : ℝ // 0 < l}) (i : Fin 2)
    (a c n : ℕ) :
    inner ℝ (mainAffineFlatBoundaryTestGradient m a c)
      (parentBoundaryRawLoadOperator (originCube 2 m) b L
        (mainFlatRotatedBasis i) (gaussEnumerated whiteBasis n)) =
      centeredCubeScale m *
        (∫ y in openCubeSet bflatUnitSquare,
          vecDot (bflatSquareSineGradientUnitField a c y)
            (q3Convolution b L h3Zero (gaussEnumerated whiteBasis n)
              (centeredCubeScale m • y) • mainFlatRotatedBasis i) ∂volume) := by
  let Q := originCube 2 m
  let R := centeredCubeScale m
  let w := gaussEnumerated whiteBasis n
  let v := mainFlatRotatedBasis i
  let hload := old_signed_rotated_raw_load_memL2 Q b L w i
  have hraw : parentBoundaryRawLoadOperator Q b L v w =
      toHilbertVectorL2OfVecField hload := by
    apply Lp.ext
    filter_upwards [parent_boundary_raw_load_operator_coeFn Q b L v w,
      coeFn_toHilbertVectorL2OfVecField hload] with x h₁ h₂
    rw [h₁, h₂]
    rfl
  let hp := (mainAffineFlatBoundaryTestPotential m a c).toH1Function.grad_memVectorL2
  rw [hraw]
  change inner ℝ (toHilbertVectorL2OfVecField hp)
    (toHilbertVectorL2OfVecField hload) = _
  rw [inner_toHilbertVectorL2OfVecField_eq_integral hp hload]
  let F (y : Vec 2) := vecDot (bflatSquareSineGradientUnitField a c y)
    (q3Convolution b L h3Zero w (R • y) • v)
  have hcancel (x : Vec 2) : R • (R⁻¹ • x) = x := by
    rw [smul_smul]
    change (centeredCubeScale m * (centeredCubeScale m)⁻¹) • x = x
    rw [mul_inv_cancel₀ (centeredCubeScale_ne_zero m), one_smul]
  calc
    _ = ∫ x in openCubeSet Q, R⁻¹ * F (R⁻¹ • x) ∂volume := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [mainAffineFlatBoundaryTestPotential_grad]
      dsimp only [F]
      rw [hcancel]
      rw [vecDot_smul_left]
    _ = R⁻¹ * (∫ x in openCubeSet Q, F (R⁻¹ • x) ∂volume) := by
      rw [integral_const_mul]
    _ = R⁻¹ * (R ^ 2 * ∫ y in openCubeSet (originCube 2 0), F y ∂volume) := by
      rw [main_affine_flat_boundary_setIntegral_dilation m F]
    _ = R * (∫ y in openCubeSet bflatUnitSquare, F y ∂volume) := by
      rw [show openCubeSet (originCube 2 0) = openCubeSet bflatUnitSquare by
        exact main_affine_flat_boundary_unit_domain]
      field_simp [centeredCubeScale_ne_zero m]

private theorem main_affine_flat_boundary_pullback_value
    (m : ℤ) (b : ℝ) (L : {l : ℝ // 0 < l}) (n : ℕ)
    (x : bflatClosedRectangle) :
    mainAffineFlatBoundaryPullback
        ⟨centeredCubeScale m, centeredCubeScale_pos m⟩ b L
        (Gaussian.q3H3Directions
          (-(centeredCubeScale m) / 2) ((centeredCubeScale m) / 2)
          (-(centeredCubeScale m) / 2) ((centeredCubeScale m) / 2) b L
          whiteBasis n) x =
      q3Convolution b L h3Zero (gaussEnumerated whiteBasis n)
        (centeredCubeScale m • x.1) := by
  let R : {r : ℝ // 0 < r} := ⟨centeredCubeScale m, centeredCubeScale_pos m⟩
  let a := -R.1 / 2
  let c := R.1 / 2
  have h := Gaussian.q3H3Directions_value_eq_convolution a c a c b
    (by change -R.1 / 2 < R.1 / 2; linarith [R.2])
    (by change -R.1 / 2 < R.1 / 2; linarith [R.2]) L n
  have hpoint := congrArg
    (fun f : C(Gaussian.closedRectangle a c a c, ℝ) =>
      f (mainAffineFlatBoundaryScaleMap R x)) h
  change Gaussian.q3H3RangeValue a c a c b L
      (Gaussian.q3H3Directions a c a c b L whiteBasis n)
      (mainAffineFlatBoundaryScaleMap R x) = _ at hpoint
  rw [Gaussian.q3ContinuousOperator_apply] at hpoint
  change Gaussian.q3H3RangeValue
      (-(centeredCubeScale m) / 2) ((centeredCubeScale m) / 2)
      (-(centeredCubeScale m) / 2) ((centeredCubeScale m) / 2) b L
      (Gaussian.q3H3Directions
        (-(centeredCubeScale m) / 2) ((centeredCubeScale m) / 2)
        (-(centeredCubeScale m) / 2) ((centeredCubeScale m) / 2) b L
        whiteBasis n)
      (mainAffineFlatBoundaryScaleMap
        ⟨centeredCubeScale m, centeredCubeScale_pos m⟩ x) = _
  exact hpoint

private theorem main_affine_flat_boundary_mode_coefficient
    (m : ℤ) (b : ℝ) (L : {l : ℝ // 0 < l})
    (i : Fin 2) (a c n : ℕ) :
    inner ℝ (mainAffineFlatBoundaryTestGradient m a c)
      (parentBoundaryRawLoadOperator (originCube 2 m) b L
        (mainFlatRotatedBasis i) (gaussEnumerated whiteBasis n)) =
      centeredCubeScale m * bflatObservation (bflatModeObservationWeight i a c)
        (mainAffineFlatBoundaryPullback
          ⟨centeredCubeScale m, centeredCubeScale_pos m⟩ b L
          (Gaussian.q3H3Directions
            (-(centeredCubeScale m) / 2) ((centeredCubeScale m) / 2)
            (-(centeredCubeScale m) / 2) ((centeredCubeScale m) / 2) b L
            whiteBasis n)) := by
  let R := centeredCubeScale m
  let e : {r : ℝ // 0 < r} := ⟨R, centeredCubeScale_pos m⟩
  let d := Gaussian.q3H3Directions (-R / 2) (R / 2) (-R / 2) (R / 2)
    b L whiteBasis n
  let T := mainAffineFlatBoundaryPullback e b L
  have hint :
      (∫ y in openCubeSet bflatUnitSquare,
        vecDot (bflatSquareSineGradientUnitField a c y)
          (q3Convolution b L h3Zero (gaussEnumerated whiteBasis n)
            (R • y) • mainFlatRotatedBasis i) ∂volume) =
      bflatObservation (bflatModeObservationWeight i a c) (T d) := by
    rw [← main_affine_flat_boundary_unit_observation i a c (T d)]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem
      (isOpen_openCubeSet bflatUnitSquare).measurableSet] with y hy
    have hclamp : (bflatClamp y).1 = y := by
      change bflatClampVec y = y
      exact bflatClampVec_eq_self_of_mem hy
    change vecDot (bflatSquareSineGradientUnitField a c y)
        (q3Convolution b L h3Zero (gaussEnumerated whiteBasis n)
          (R • y) • mainFlatRotatedBasis i) =
      vecDot (bflatSquareSineGradientUnitField a c y)
        (T d (bflatClamp y) • mainFlatRotatedBasis i)
    rw [main_affine_flat_boundary_pullback_value m b L n (bflatClamp y), hclamp]
  rw [main_affine_flat_boundary_pairing_dilation m b L i a c n]
  change R * _ = R * _
  rw [hint]

private theorem main_affine_flat_boundary_native_bessel
    (m : ℤ) (b : ℝ) (L : {l : ℝ // 0 < l})
    (i : Fin 2) (N n : ℕ) :
    centeredCubeScale m ^ 2 *
      (∑ p ∈ Finset.range N ×ˢ Finset.range N,
        (bflatObservation (bflatModeObservationWeight i p.1 p.2)
          (mainAffineFlatBoundaryPullback
            ⟨centeredCubeScale m, centeredCubeScale_pos m⟩ b L
            (Gaussian.q3H3Directions
              (-(centeredCubeScale m) / 2) ((centeredCubeScale m) / 2)
              (-(centeredCubeScale m) / 2) ((centeredCubeScale m) / 2) b L
              whiteBasis n))) ^ 2) ≤
      ‖parentBoundaryDirichletLoadOperator (originCube 2 m) b L
        (mainFlatRotatedBasis i) (gaussEnumerated whiteBasis n)‖ ^ 2 := by
  let S := Finset.range N ×ˢ Finset.range N
  let R := centeredCubeScale m
  let e : {r : ℝ // 0 < r} := ⟨R, centeredCubeScale_pos m⟩
  let d := Gaussian.q3H3Directions (-R / 2) (R / 2) (-R / 2) (R / 2)
    b L whiteBasis n
  let T := mainAffineFlatBoundaryPullback e b L
  have hbase := mainAffineFlatBoundary_finite_bessel m b L
    (mainFlatRotatedBasis i) (gaussEnumerated whiteBasis n) N
  have hsum :
      (∑ p ∈ S,
        (inner ℝ (mainAffineFlatBoundaryTestGradient m p.1 p.2)
          (parentBoundaryRawLoadOperator (originCube 2 m) b L
            (mainFlatRotatedBasis i) (gaussEnumerated whiteBasis n))) ^ 2) =
        R ^ 2 * (∑ p ∈ S, (bflatObservation (bflatModeObservationWeight i p.1 p.2)
          (T d)) ^ 2) := by
    calc
      _ = ∑ p ∈ S,
          (R * bflatObservation (bflatModeObservationWeight i p.1 p.2)
            (T d)) ^ 2 := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [main_affine_flat_boundary_mode_coefficient m b L i p.1 p.2 n]
      _ = _ := by
        simp only [mul_pow]
        rw [Finset.mul_sum]
  rw [hsum] at hbase
  simpa only [S, R, e, d, T] using hbase

private theorem main_affine_flat_boundary_single_le_sum
    {α : Type*} (S : Finset α) (f : α → ℝ) (p : α)
    (hp : p ∈ S) (hf : ∀ q ∈ S, 0 ≤ f q) :
    f p ≤ ∑ q ∈ S, f q :=
  Finset.single_le_sum hf hp

private theorem main_affine_flat_boundary_mode_variance_le_native
    (m : ℤ) (b : ℝ) (L : {l : ℝ // 0 < l}) (d N : ℕ)
    (hratio : L.1 / centeredCubeScale m =
      (ASDExplicitGamma.Numerics.Model.q3ModeLength d : ℝ))
    (i : Fin 2) :
    centeredCubeScale m ^ 2 *
      (∑ p ∈ Finset.range N ×ˢ Finset.range N,
        bflatModeSeriesVariance whiteBasis i p.1 p.2 b
          (bflatQ3ModeScale d)) ≤
      ∑' n : ℕ,
        ‖parentBoundaryDirichletLoadOperator (originCube 2 m) b L
          (mainFlatRotatedBasis i) (gaussEnumerated whiteBasis n)‖ ^ 2 := by
  let R := centeredCubeScale m
  let Q := originCube 2 m
  let S := Finset.range N ×ˢ Finset.range N
  let e : {r : ℝ // 0 < r} := ⟨R, centeredCubeScale_pos m⟩
  let dirs := Gaussian.q3H3Directions (-R / 2) (R / 2) (-R / 2) (R / 2)
    b L whiteBasis
  let T := mainAffineFlatBoundaryPullback e b L
  let Tload := parentBoundaryDirichletLoadOperator Q b L (mainFlatRotatedBasis i)
  let F (n : ℕ) := ∑ p ∈ S,
    (bflatObservation (bflatModeObservationWeight i p.1 p.2) (T (dirs n))) ^ 2
  have hR2 : 0 < R ^ 2 := sq_pos_of_pos (centeredCubeScale_pos m)
  have hdirBase := parent_boundary_dirichlet_load_trace_summable
    whiteBasis Q b L (mainFlatRotatedBasis i)
  let dirBase (j : whiteBasisIndex) := Tload (whiteBasis j)
  have hdir : Summable (fun n : ℕ => ‖Tload (gaussEnumerated whiteBasis n)‖ ^ 2) := by
    have henum := Gaussian.enumerated_summable_sq dirBase (by simpa only [dirBase, Tload, Q] using hdirBase)
    have hmap (n : ℕ) : Tload (gaussEnumerated whiteBasis n) =
        Gaussian.gaussEnumerated dirBase n := by
      change Tload (gaussEnumerated whiteBasis n) =
        Gaussian.gaussEnumerated (fun j => Tload (whiteBasis j)) n
      exact Gaussian.enumerated_map Tload whiteBasis n
    have heq : (fun n : ℕ => ‖Tload (gaussEnumerated whiteBasis n)‖ ^ 2) =
        (fun n => ‖Gaussian.gaussEnumerated dirBase n‖ ^ 2) := by
      funext n
      rw [hmap]
    rw [heq]
    exact henum
  have hBessel (n : ℕ) : R ^ 2 * F n ≤
      ‖Tload (gaussEnumerated whiteBasis n)‖ ^ 2 := by
    simpa only [F, Tload, Q, R, e, dirs, T] using
      main_affine_flat_boundary_native_bessel m b L i N n
  have hFnonneg (n : ℕ) : 0 ≤ F n := by
    apply Finset.sum_nonneg
    intro p hp
    exact sq_nonneg _
  have hFbound (n : ℕ) : F n ≤ (R ^ 2)⁻¹ *
      ‖Tload (gaussEnumerated whiteBasis n)‖ ^ 2 := by
    calc
      F n = (R ^ 2)⁻¹ * (R ^ 2 * F n) := by
        have hinv : (R ^ 2)⁻¹ * R ^ 2 = 1 :=
          inv_mul_cancel₀ (ne_of_gt hR2)
        calc
          F n = 1 * F n := by ring
          _ = ((R ^ 2)⁻¹ * R ^ 2) * F n := by rw [hinv]
          _ = _ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hBessel n)
        (inv_nonneg.mpr hR2.le)
  have hFsummable : Summable F :=
    Summable.of_nonneg_of_le hFnonneg hFbound (hdir.mul_left ((R ^ 2)⁻¹))
  have hcoord (p : ℕ × ℕ) (hp : p ∈ S) :
      Summable (fun n : ℕ =>
        (bflatObservation (bflatModeObservationWeight i p.1 p.2) (T (dirs n))) ^ 2) := by
    have hbound (n : ℕ) :
        (bflatObservation (bflatModeObservationWeight i p.1 p.2) (T (dirs n))) ^ 2 ≤ F n := by
      change (bflatObservation (bflatModeObservationWeight i p.1 p.2)
          (T (dirs n))) ^ 2 ≤
        ∑ q ∈ S,
          (bflatObservation (bflatModeObservationWeight i q.1 q.2)
            (T (dirs n))) ^ 2
      exact main_affine_flat_boundary_single_le_sum S
        (fun q => (bflatObservation (bflatModeObservationWeight i q.1 q.2)
          (T (dirs n))) ^ 2) p hp
        (fun q hq => sq_nonneg _)
    apply Summable.of_nonneg_of_le (fun n => sq_nonneg _)
      hbound hFsummable
  have hswap := Summable.tsum_finsetSum (fun p hp => hcoord p hp)
  have hscale (p : ℕ × ℕ) :
      (∑' n : ℕ,
        (bflatObservation (bflatModeObservationWeight i p.1 p.2) (T (dirs n))) ^ 2) =
      bflatModeSeriesVariance whiteBasis i p.1 p.2 b (bflatQ3ModeScale d) := by
    simpa only [R, e, dirs, T] using
      main_affine_flat_boundary_scale_covariance whiteBasis e b L d hratio i p.1 p.2
  have hsum :
      (∑ p ∈ S, bflatModeSeriesVariance whiteBasis i p.1 p.2 b
        (bflatQ3ModeScale d)) = ∑' n : ℕ, F n := by
    calc
      _ = ∑ p ∈ S,
          ∑' n : ℕ,
            (bflatObservation (bflatModeObservationWeight i p.1 p.2)
              (T (dirs n))) ^ 2 := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [hscale]
      _ = _ := hswap.symm
  calc
    _ = R ^ 2 * ∑' n : ℕ, F n := by rw [hsum]
    _ = ∑' n : ℕ, R ^ 2 * F n := by rw [← tsum_mul_left]
    _ ≤ ∑' n : ℕ, ‖Tload (gaussEnumerated whiteBasis n)‖ ^ 2 :=
      Summable.tsum_le_tsum hBessel (hFsummable.mul_left (R ^ 2)) hdir

private theorem main_affine_flat_boundary_projection_lower
    (m : ℤ) (b : ℝ) (L : {l : ℝ // 0 < l}) (d N : ℕ)
    (hratio : L.1 / centeredCubeScale m =
      (ASDExplicitGamma.Numerics.Model.q3ModeLength d : ℝ)) :
    b ^ 2 * ASDExplicitGamma.Numerics.Model.q3Projection d N ≤
      parentBoundaryDirichletEnergy (originCube 2 m) b L := by
  let R := centeredCubeScale m
  let Q := originCube 2 m
  let S := Finset.range N ×ˢ Finset.range N
  let Tload (v : Vec 2) := parentBoundaryDirichletLoadOperator Q b L v
  have hR2 : 0 < R ^ 2 := sq_pos_of_pos (centeredCubeScale_pos m)
  have hrotTrace :
      (∑ i : Fin 2, ∑' n : ℕ,
        ‖Tload (mainFlatRotatedBasis i) (gaussEnumerated whiteBasis n)‖ ^ 2) =
      ∑ i : Fin 2, ∑' j : whiteBasisIndex,
        ‖Tload (basisVec i) (whiteBasis j)‖ ^ 2 := by
    rw [Fin.sum_univ_two, Fin.sum_univ_two]
    have hEnum (v : Vec 2) :
        (∑' n : ℕ, ‖Tload v (gaussEnumerated whiteBasis n)‖ ^ 2) =
          ∑' j : whiteBasisIndex, ‖Tload v (whiteBasis j)‖ ^ 2 := by
      exact Gaussian.enumerated_tsum_apply whiteBasis
        (fun w => ‖Tload v w‖ ^ 2) (by simp)
    rw [old_signed_rotated_basis_zero, old_signed_rotated_basis_one]
    have hminus (n : ℕ) :
        ‖Tload (-basisVec 0) (gaussEnumerated whiteBasis n)‖ ^ 2 =
          ‖Tload (basisVec 0) (gaussEnumerated whiteBasis n)‖ ^ 2 := by
      dsimp only [Tload]
      change ‖parentBoundaryDirichletLoadOperator Q b L (-basisVec 0)
          (gaussEnumerated whiteBasis n)‖ ^ 2 =
        ‖parentBoundaryDirichletLoadOperator Q b L (basisVec 0)
          (gaussEnumerated whiteBasis n)‖ ^ 2
      rw [parent_boundary_dirichlet_load_neg]
      simp
    calc
      _ = (∑' n : ℕ,
          ‖Tload (basisVec 1) (gaussEnumerated whiteBasis n)‖ ^ 2) +
          ∑' n : ℕ, ‖Tload (basisVec 0) (gaussEnumerated whiteBasis n)‖ ^ 2 := by
        congr 1
        exact tsum_congr hminus
      _ = _ := by rw [hEnum (basisVec 1), hEnum (basisVec 0)]; ring
  have htrace : cubeVolume Q * parentBoundaryDirichletEnergy Q b L =
      ∑ i : Fin 2, ∑' j : whiteBasisIndex,
        ‖Tload (basisVec i) (whiteBasis j)‖ ^ 2 := by
    rw [parent_boundary_dirichlet_energy_gram_trace]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [parentBoundaryDirichletGram, real_inner_self_eq_norm_sq]
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt (cubeVolume_pos Q)), one_mul]
  have hnativeTrace :
      (∑ i : Fin 2, ∑' n : ℕ,
        ‖Tload (mainFlatRotatedBasis i) (gaussEnumerated whiteBasis n)‖ ^ 2) =
        cubeVolume Q * parentBoundaryDirichletEnergy Q b L := by
    rw [hrotTrace, htrace]
  have hper (i : Fin 2) :
      R ^ 2 * (∑ p ∈ S,
          bflatModeSeriesVariance whiteBasis i p.1 p.2 b
            (bflatQ3ModeScale d)) ≤
        ∑' n : ℕ,
          ‖Tload (mainFlatRotatedBasis i) (gaussEnumerated whiteBasis n)‖ ^ 2 := by
    simpa only [R, S, Tload] using
      main_affine_flat_boundary_mode_variance_le_native m b L d N hratio i
  have hsum :
      (∑ i : Fin 2, R ^ 2 * (∑ p ∈ S,
        bflatModeSeriesVariance whiteBasis i p.1 p.2 b
          (bflatQ3ModeScale d))) ≤
      ∑ i : Fin 2, ∑' n : ℕ,
        ‖Tload (mainFlatRotatedBasis i) (gaussEnumerated whiteBasis n)‖ ^ 2 := by
    apply Finset.sum_le_sum
    intro i hi
    exact hper i
  have htotal : R ^ 2 *
        (∑ i : Fin 2, ∑ p ∈ S,
          bflatModeSeriesVariance whiteBasis i p.1 p.2 b
            (bflatQ3ModeScale d)) ≤
      cubeVolume Q * parentBoundaryDirichletEnergy Q b L := by
    calc
      _ = ∑ i : Fin 2, R ^ 2 * (∑ p ∈ S,
          bflatModeSeriesVariance whiteBasis i p.1 p.2 b
            (bflatQ3ModeScale d)) := by rw [Finset.mul_sum]
      _ ≤ _ := hsum.trans_eq hnativeTrace
  have hvolume : cubeVolume Q = R ^ 2 := by
    dsimp [Q, R]
    rw [cubeVolume_eq_scaleFactor_pow, cubeScaleFactor_originCube]
    simp [centeredCubeScale]
  rw [hvolume] at htotal
  have hfinite :
      (∑ i : Fin 2, ∑ p ∈ S,
        bflatModeSeriesVariance whiteBasis i p.1 p.2 b
          (bflatQ3ModeScale d)) = b ^ 2 *
        ASDExplicitGamma.Numerics.Model.q3Projection d N := by
    rw [Fin.sum_univ_two]
    have hprod (i : Fin 2) :
        (∑ p ∈ S,
          bflatModeSeriesVariance whiteBasis i p.1 p.2 b
            (bflatQ3ModeScale d)) =
        ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
          bflatModeSeriesVariance whiteBasis i m n b (bflatQ3ModeScale d) := by
      dsimp [S]
      exact Finset.sum_product' (Finset.range N) (Finset.range N)
        (fun m n => bflatModeSeriesVariance whiteBasis i m n b
          (bflatQ3ModeScale d))
    rw [hprod 0, hprod 1]
    calc
      _ = ∑ m ∈ Finset.range N,
          (∑ n ∈ Finset.range N,
            bflatModeSeriesVariance whiteBasis 0 m n b (bflatQ3ModeScale d) +
            ∑ n ∈ Finset.range N,
            bflatModeSeriesVariance whiteBasis 1 m n b (bflatQ3ModeScale d)) := by
        rw [← Finset.sum_add_distrib]
      _ = ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
          (bflatModeSeriesVariance whiteBasis 0 m n b (bflatQ3ModeScale d) +
            bflatModeSeriesVariance whiteBasis 1 m n b (bflatQ3ModeScale d)) := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [← Finset.sum_add_distrib]
      _ = _ := by
        simpa [bflatQ3ModeScale] using
          bflatModeSeriesVariance_finite_sum_eq_q3Projection_scaled
            (e := whiteBasis) d N b
  rw [hfinite] at htotal
  exact (mul_le_mul_iff_right₀ hR2).mp htotal

private theorem main_affine_flat_boundary_projection_tsum_le_native
    (m : ℤ) (b : ℝ) (L : {l : ℝ // 0 < l}) (d : ℕ)
    (hratio : L.1 / centeredCubeScale m =
      (ASDExplicitGamma.Numerics.Model.q3ModeLength d : ℝ)) :
    b ^ 2 * (∑' p : ℕ × ℕ, bflatQ3ModeProjectionTerm d p) ≤
      parentBoundaryDirichletEnergy (originCube 2 m) b L := by
  have hs := bflatQ3ModeProjectionTerm_summable d
  let f (p : ℕ × ℕ) := b ^ 2 * bflatQ3ModeProjectionTerm d p
  have hscaled : Summable f := by
    simpa only [f] using hs.mul_left (b ^ 2)
  have hβ : 0 ≤ b ^ 2 := sq_nonneg b
  have hterm (p : ℕ × ℕ) : 0 ≤ bflatQ3ModeProjectionTerm d p := by
    unfold bflatQ3ModeProjectionTerm
    exact mul_nonneg (mul_nonneg (by norm_num) (by
      unfold ASDExplicitGamma.Numerics.Model.modeWeight
      positivity)) (mul_nonneg (bflatQ3ModeCosine_nonneg d p.1)
        (bflatQ3ModeSine_nonneg d p.2))
  rw [← tsum_mul_left]
  apply hscaled.tsum_le_of_sum_le
  intro s
  let N := s.sup (fun p : ℕ × ℕ => max p.1 p.2) + 1
  have hsub : s ⊆ Finset.range N ×ˢ Finset.range N := by
    intro p hp
    simp only [Finset.mem_product, Finset.mem_range]
    have hmax : max p.1 p.2 ≤ s.sup (fun q : ℕ × ℕ => max q.1 q.2) :=
      Finset.le_sup (f := fun q : ℕ × ℕ => max q.1 q.2) hp
    constructor <;> dsimp [N] <;> omega
  have hsubsetSum := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun p hp _ => mul_nonneg hβ (hterm p))
  have hrect :
      (∑ p ∈ Finset.range N ×ˢ Finset.range N,
        bflatQ3ModeProjectionTerm d p) =
        ASDExplicitGamma.Numerics.Model.q3Projection d N := by
    calc
      _ = ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
          bflatQ3ModeProjectionTerm d (m,n) :=
        Finset.sum_product' (Finset.range N) (Finset.range N)
          (fun m n => bflatQ3ModeProjectionTerm d (m,n))
      _ = _ := by
        unfold ASDExplicitGamma.Numerics.Model.q3Projection
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m hm
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        simp [bflatQ3ModeProjectionTerm,
          ASDExplicitGamma.Numerics.Model.modeWeight]
        ring
  have hrectScaled :
      (∑ p ∈ Finset.range N ×ˢ Finset.range N, f p) =
        b ^ 2 * ASDExplicitGamma.Numerics.Model.q3Projection d N := by
    calc
      _ = b ^ 2 * (∑ p ∈ Finset.range N ×ˢ Finset.range N,
          bflatQ3ModeProjectionTerm d p) := by
        simp only [f]
        rw [Finset.mul_sum]
      _ = _ := by rw [hrect]
  calc
    _ ≤ ∑ p ∈ Finset.range N ×ˢ Finset.range N, f p := hsubsetSum
    _ = b ^ 2 * ASDExplicitGamma.Numerics.Model.q3Projection d N := hrectScaled
    _ ≤ parentBoundaryDirichletEnergy (originCube 2 m) b L :=
      main_affine_flat_boundary_projection_lower m b L d N hratio

private theorem main_affine_flat_boundary_mode_term_eq_tail
    (d : ℕ) (p : ℕ × ℕ) :
    bflatQ3ModeProjectionTerm d p =
      2 * (ASDExplicitGamma.Numerics.Model.modeWeight p.1 p.2 *
        ((ASDExplicitGamma.Numerics.Model.q3ModeSine d p.1 -
          ASDExplicitGamma.Numerics.Model.q3ModeDifference d p.1) *
          ASDExplicitGamma.Numerics.Model.q3ModeSine d p.2)) := by
  have hmode : ASDExplicitGamma.Numerics.Model.q3ModeCosine d p.1 =
      ASDExplicitGamma.Numerics.Model.q3ModeSine d p.1 -
        ASDExplicitGamma.Numerics.Model.q3ModeDifference d p.1 := by
    unfold ASDExplicitGamma.Numerics.Model.q3ModeDifference
    ring
  rw [bflatQ3ModeProjectionTerm, hmode]
  ring

private theorem main_affine_flat_boundary_unit_tail (d : ℕ) :
    2 - 2 * (∑' p : ℕ × ℕ, bflatQ3ModeProjectionTerm d p) ≤
      min 2 ((429 / 175 : ℝ) *
          (ASDExplicitGamma.Numerics.Model.q3ModeLength d : ℝ) -
        (7 / 15 : ℝ) *
          (ASDExplicitGamma.Numerics.Model.q3ModeLength d : ℝ) ^ 2) := by
  have hsum : (∑' p : ℕ × ℕ, bflatQ3ModeProjectionTerm d p) =
      ∑' p : ℕ × ℕ, 2 * (ASDExplicitGamma.Numerics.Model.modeWeight p.1 p.2 *
        ((ASDExplicitGamma.Numerics.Model.q3ModeSine d p.1 -
          ASDExplicitGamma.Numerics.Model.q3ModeDifference d p.1) *
          ASDExplicitGamma.Numerics.Model.q3ModeSine d p.2)) := by
    apply tsum_congr
    intro p
    exact main_affine_flat_boundary_mode_term_eq_tail d p
  rw [hsum, tsum_mul_left]
  convert bflatQ3_mode_tail d using 1 <;> ring

private theorem main_affine_flat_boundary_exact_cap_from_projection
    (b Y : ℝ) (d N : ℕ) (c : ℝ) (hb : 0 < b)
    (hprojection : b ^ 2 * ASDExplicitGamma.Numerics.Model.q3Projection d N ≤ Y)
    (hcap : 2 - 2 * ASDExplicitGamma.Numerics.Model.q3Projection d N < c) :
    2 * b ^ 2 - 2 * Y ≤ b ^ 2 * c := by
  have hlower : 2 * b ^ 2 - 2 * Y ≤
      b ^ 2 * (2 - 2 * ASDExplicitGamma.Numerics.Model.q3Projection d N) := by
    nlinarith [hprojection]
  have hstrict := mul_lt_mul_of_pos_left hcap (sq_pos_of_pos hb)
  exact le_of_lt (lt_of_le_of_lt hlower hstrict)

theorem old_hessian_flat_boundary_native_cap_all
    (m : ℤ) (b : ℝ) (L : {l : ℝ // 0 < l}) (d : ℕ) (hb : 0 < b)
    (hratio : L.1 / centeredCubeScale m =
      (ASDExplicitGamma.Numerics.Model.q3ModeLength d : ℝ)) :
    oldSignedFlatBoundaryEnergy (originCube 2 m) b L ≤
      b ^ 2 * mainAffineFlatBoundaryCapQ d := by
  let Y := parentBoundaryDirichletEnergy (originCube 2 m) b L
  have hbase := parent_boundary_flat_baseline (originCube 2 m) b L
  have henergy (N : ℕ) : b ^ 2 *
      ASDExplicitGamma.Numerics.Model.q3Projection d N ≤ Y := by
    simpa only [Y] using
      main_affine_flat_boundary_projection_lower m b L d N hratio
  have hcapExact (N : ℕ) (c : ℝ)
      (hcap : 2 - 2 * ASDExplicitGamma.Numerics.Model.q3Projection d N < c) :
      2 * b ^ 2 - 2 * Y ≤ b ^ 2 * c :=
    main_affine_flat_boundary_exact_cap_from_projection b Y d N c hb
      (henergy N) hcap
  by_cases h0 : d = 0
  · subst d
    have h := hcapExact 32 _ bflat_projection_exact_cap_j0'
    rw [hbase.1]
    simpa [mainAffineFlatBoundaryCapQ, Y] using h
  by_cases h1 : d = 1
  · subst d
    have h := hcapExact 32 _ bflat_projection_exact_cap_j1'
    rw [hbase.1]
    simpa [mainAffineFlatBoundaryCapQ, Y] using h
  by_cases h2 : d = 2
  · subst d
    have h := hcapExact 64 _ bflat_projection_exact_cap_j2'
    rw [hbase.1]
    simpa [mainAffineFlatBoundaryCapQ, Y] using h
  by_cases h3 : d = 3
  · subst d
    have h := hcapExact 256 _ bflat_projection_exact_cap_j3'
    rw [hbase.1]
    simpa [mainAffineFlatBoundaryCapQ, Y] using h
  by_cases h4 : d = 4
  · subst d
    have h := hcapExact 512 _ bflat_projection_exact_cap_j4'
    rw [hbase.1]
    simpa [mainAffineFlatBoundaryCapQ, Y] using h
  by_cases h5 : d = 5
  · subst d
    have h := hcapExact 2048 _ bflat_projection_exact_cap_j5'
    rw [hbase.1]
    simpa [mainAffineFlatBoundaryCapQ, Y] using h
  · have hprojection := main_affine_flat_boundary_projection_tsum_le_native
      m b L d hratio
    have htail := main_affine_flat_boundary_unit_tail d
    have hmul := mul_le_mul_of_nonneg_left htail (sq_nonneg b)
    have hpoly := hmul.trans (mul_le_mul_of_nonneg_left
      (min_le_right 2 ((429 / 175 : ℝ) *
        (ASDExplicitGamma.Numerics.Model.q3ModeLength d : ℝ) -
        (7 / 15 : ℝ) *
          (ASDExplicitGamma.Numerics.Model.q3ModeLength d : ℝ) ^ 2))
      (sq_nonneg b))
    have hcap : 2 * b ^ 2 - 2 * Y ≤ b ^ 2 *
        ((429 / 175 : ℝ) *
          (ASDExplicitGamma.Numerics.Model.q3ModeLength d : ℝ) -
          (7 / 15 : ℝ) *
            (ASDExplicitGamma.Numerics.Model.q3ModeLength d : ℝ) ^ 2) := by
      nlinarith [hprojection, hpoly]
    have hbaseEnergy : oldSignedFlatBoundaryEnergy (originCube 2 m) b L =
        2 * b ^ 2 - 2 * Y := by
      simpa only [Y] using hbase.1
    rw [hbaseEnergy]
    simpa [mainAffineFlatBoundaryCapQ, h0, h1, h2, h3, h4, h5] using hcap


/-- The all-observer Bflat cap at the original fine observer gap 128:
`B_flat ≤ b² * q` with `q = (429/175) 3^{-128}`. -/
theorem old_hessian_flat_boundary_q128 (m : ℤ) (b : ℝ) (hb : 0 < b) :
    oldSignedFlatBoundaryEnergy (originCube 2 (m + 129)) b (q3ModelLength (m + 1)) ≤
      b ^ 2 * ((429 / 175 : ℝ) * (1 / (3 : ℝ) ^ 128)) := by
  have hratio : (q3ModelLength (m + 1)).1 / centeredCubeScale (m + ((129 : ℕ) : ℤ)) =
      (ASDExplicitGamma.Numerics.Model.q3ModeLength 128 : ℝ) := by
    simpa only [centeredCubeScale, cubeScaleFactor_originCube] using
      main_affine_flat_boundary_model_scale m 129 (by norm_num)
  have h := old_hessian_flat_boundary_native_cap_all (m + ((129 : ℕ) : ℤ)) b
    (q3ModelLength (m + 1)) 128 hb hratio
  have hq : (ASDExplicitGamma.Numerics.Model.q3ModeLength 128 : ℝ) = 1 / (3 : ℝ) ^ 128 := by
    simp [ASDExplicitGamma.Numerics.Model.q3ModeLength]
  have hc : mainAffineFlatBoundaryCapQ 128 ≤ (429 / 175 : ℝ) * (1 / (3 : ℝ) ^ 128) := by
    unfold mainAffineFlatBoundaryCapQ
    simp only [show (128:ℕ) ≠ 0 by norm_num, show (128:ℕ) ≠ 1 by norm_num, show (128:ℕ) ≠ 2 by norm_num,
      show (128:ℕ) ≠ 3 by norm_num, show (128:ℕ) ≠ 4 by norm_num, show (128:ℕ) ≠ 5 by norm_num, if_false]
    rw [hq]
    have : (0:ℝ) ≤ (7 / 15 : ℝ) * (1 / (3 : ℝ) ^ 128) ^ 2 := by positivity
    linarith
  have h129 : ((m + ((129 : ℕ) : ℤ))) = m + 129 := by push_cast; ring
  rw [h129] at h
  exact h.trans (mul_le_mul_of_nonneg_left hc (sq_nonneg b))

end

end ASDExplicitGamma.Main
