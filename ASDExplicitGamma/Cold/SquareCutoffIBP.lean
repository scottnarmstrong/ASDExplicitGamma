module

public import ASDExplicitGamma.Cold.LipschitzDivergence
public import ASDExplicitGamma.Cold.BoundedL2Multiplier
public import ASDExplicitGamma.Cold.PlateauOnSquare

/-! # The square cutoff integration-by-parts identity -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Homogenization
open ASDExplicitGamma.Triadic
open scoped BigOperators ENNReal NNReal

namespace ASDExplicitGamma.Cold

/-- Open and closed native squares differ only by a null set. -/
theorem openCubeSet_ae_eq_closedSquare (Q : TriadicCube 2) :
    openCubeSet Q =ᵐ[volume] closedSquare Q := by
  rw [openCubeSet_eq_box]
  exact Measure.univ_pi_Ioo_ae_eq_Icc

/-- A factor supported on the closed square localizes its global integral to the open square. -/
theorem integral_cutoff_localize (Q : TriadicCube 2) {φ : Vec 2 → ℝ}
    (hφs : tsupport φ ⊆ closedSquare Q) (g : Vec 2 → ℝ) :
    (∫ x, φ x * g x) = ∫ x in openCubeSet Q, φ x * g x := by
  symm
  apply setIntegral_eq_integral_of_ae_compl_eq_zero
  filter_upwards [openCubeSet_ae_eq_closedSquare Q] with x hx hnot
  have hclosed : x ∉ closedSquare Q := fun h => hnot ((Iff.of_eq hx).mpr h)
  rw [image_eq_zero_of_notMem_tsupport (fun h => hclosed (hφs h)), zero_mul]

/-- The weak gradient also vanishes almost everywhere off the square. -/
theorem integral_cutoff_gradient_localize (Q : TriadicCube 2) {φ : Vec 2 → ℝ} {C : ℝ≥0}
    (hφ : LipschitzWith C φ) (hφs : tsupport φ ⊆ closedSquare Q)
    (i : Fin 2) (g : Vec 2 → ℝ) :
    (∫ x, lipschitzWeakGradient φ x i * g x) =
      ∫ x in openCubeSet Q, lipschitzWeakGradient φ x i * g x := by
  symm
  apply setIntegral_eq_integral_of_ae_compl_eq_zero
  filter_upwards [openCubeSet_ae_eq_closedSquare Q, lipschitzWeakGradient_ae_eq_fderiv hφ]
    with x hx hgrad hnot
  have hclosed : x ∉ closedSquare Q := fun h => hnot ((Iff.of_eq hx).mpr h)
  rw [hgrad i, fderiv_of_notMem_tsupport ℝ (fun h => hclosed (hφs h))]
  simp

/-- Localized smooth transport integration by parts. Only the scalar cutoff is Lipschitz;
the source's zero boundary condition is encoded by its global continuous zero extension. -/
theorem square_cutoff_ibp_smooth (Q : TriadicCube 2) {φ u w : Vec 2 → ℝ} {C : ℝ≥0}
    (hφ : LipschitzWith C φ) (hφs : tsupport φ ⊆ closedSquare Q)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hw : ContDiff ℝ (⊤ : ℕ∞) w) :
    (∫ x in openCubeSet Q, φ x * (-(smoothPartial u 0 x * smoothPartial w 1 x) +
      smoothPartial u 1 x * smoothPartial w 0 x)) =
      -((∫ x in openCubeSet Q, lipschitzWeakGradient φ x 0 * (-(u x * smoothPartial w 1 x))) +
        (∫ x in openCubeSet Q, lipschitzWeakGradient φ x 1 * (u x * smoothPartial w 0 x))) := by
  let χ := faceCompactifyingCutoff Q
  let uc : Vec 2 → ℝ := fun x => χ x * u x
  have huc : ContDiff ℝ (⊤ : ℕ∞) uc := (faceCompactifyingCutoff Q).smooth.mul hu
  have hcompact : HasCompactSupport uc := (faceCompactifyingCutoff Q).hasCompactSupport.mul_right
  have hlocal (x : Vec 2) (hx : x ∈ openCubeSet Q) : uc =ᶠ[𝓝 x] u := by
    filter_upwards [(isOpen_openCubeSet Q).mem_nhds hx] with y hy
    change faceCompactifyingCutoff Q y * u y = u y
    rw [faceCompactifyingCutoff_eq_one_on_openCubeSet Q hy, one_mul]
  have h := lipschitz_transport_ibp_smooth hφ huc hcompact hw
  rw [integral_cutoff_localize Q hφs,
    integral_cutoff_gradient_localize Q hφ hφs 0,
    integral_cutoff_gradient_localize Q hφ hφs 1] at h
  have hleft : (∫ x in openCubeSet Q, φ x * (-(smoothPartial uc 0 x * smoothPartial w 1 x) +
      smoothPartial uc 1 x * smoothPartial w 0 x)) =
      ∫ x in openCubeSet Q, φ x * (-(smoothPartial u 0 x * smoothPartial w 1 x) +
      smoothPartial u 1 x * smoothPartial w 0 x) := by
    apply setIntegral_congr_fun (measurableSet_openCubeSet Q)
    intro x hx
    dsimp only
    unfold smoothPartial
    rw [(hlocal x hx).fderiv_eq]
  have hright0 : (∫ x in openCubeSet Q,
      lipschitzWeakGradient φ x 0 * (-(uc x * smoothPartial w 1 x))) =
      ∫ x in openCubeSet Q, lipschitzWeakGradient φ x 0 * (-(u x * smoothPartial w 1 x)) := by
    apply setIntegral_congr_fun (measurableSet_openCubeSet Q)
    intro x hx
    dsimp only
    rw [(hlocal x hx).eq_of_nhds]
  have hright1 : (∫ x in openCubeSet Q,
      lipschitzWeakGradient φ x 1 * (uc x * smoothPartial w 0 x)) =
      ∫ x in openCubeSet Q, lipschitzWeakGradient φ x 1 * (u x * smoothPartial w 0 x) := by
    apply setIntegral_congr_fun (measurableSet_openCubeSet Q)
    intro x hx
    dsimp only
    rw [(hlocal x hx).eq_of_nhds]
  rwa [hleft, hright0, hright1] at h

end ASDExplicitGamma.Cold
