module

public import ASDExplicitGamma.Cold.PlateauWeakCutoff
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! # Integration by parts for a Lipschitz plateau cutoff -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Homogenization
open scoped BigOperators ENNReal NNReal

namespace ASDExplicitGamma.Cold

/-- Integration by parts against a compactly supported smooth vector field, with a
Lipschitz scalar factor and its actual weak derivative. -/
theorem integral_lipschitz_divergence {d : ℕ} {f : Vec d → ℝ} {C : ℝ≥0}
    (hf : LipschitzWith C f) (F : Fin d → Vec d → ℝ)
    (hF : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (F i)) (hFc : ∀ i, HasCompactSupport (F i)) :
    (∑ i : Fin d, ∫ x, lipschitzWeakGradient f x i * F i x) =
      -(∫ x, f x * ∑ i : Fin d, (fderiv ℝ (F i) x) (basisVec i)) := by
  have hid (i : Fin d) : (∫ x, lipschitzWeakGradient f x i * F i x) =
      -(∫ x, f x * (fderiv ℝ (F i) x) (basisVec i)) := by
    obtain ⟨D, hD⟩ := ContDiff.lipschitzWith_of_hasCompactSupport (hFc i) (hF i) (by simp)
    have h := hf.integral_lineDeriv_mul_eq (μ := volume) hD (hFc i) (basisVec i)
    have hd (x : Vec d) := ((hF i).differentiable (by simp)) x
    simp_rw [(hd _).lineDeriv_eq_fderiv, map_neg, neg_mul, integral_neg] at h
    change (∫ x, lineDeriv ℝ f x (basisVec i) * F i x) = _
    rw [h]
    congr 1
    congr 1
    funext x
    ring
  have hint (i : Fin d) : Integrable (fun x => f x * (fderiv ℝ (F i) x) (basisVec i)) := by
    have hc : Continuous (fun x => (fderiv ℝ (F i) x) (basisVec i)) :=
      ((hF i).continuous_fderiv (by simp)).clm_apply continuous_const
    have hcomp := (hFc i).fderiv_apply (𝕜 := ℝ) (basisVec i)
    exact (hf.continuous.mul hc).integrable_of_hasCompactSupport hcomp.mul_left
  simp_rw [hid]
  rw [Finset.sum_neg_distrib]
  congr 1
  simp_rw [Finset.mul_sum]
  exact (integral_finsetSum _ (fun i _ => hint i)).symm

/-- The two classical cross derivatives commute for smooth functions. -/
theorem planar_cross_derivatives_commute {w : Vec 2 → ℝ}
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (x : Vec 2) :
    (fderiv ℝ (fun y => (fderiv ℝ w y) (basisVec 1)) x) (basisVec 0) =
      (fderiv ℝ (fun y => (fderiv ℝ w y) (basisVec 0)) x) (basisVec 1) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ w) x :=
    ((hw.fderiv_right (m := 1) (by simp)).differentiable (by simp)) x
  rw [fderiv_clm_apply hd (differentiableAt_const (basisVec 1)),
    fderiv_clm_apply hd (differentiableAt_const (basisVec 0))]
  rw [(hasFDerivAt_const (basisVec 1) x).fderiv, (hasFDerivAt_const (basisVec 0) x).fderiv]
  simp only [ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply]
  exact (hw.contDiffAt.isSymmSndFDerivAt (by simp)).eq (basisVec 0) (basisVec 1)

/-- A coordinate partial derivative of a smooth function on the plane. -/
def smoothPartial (u : Vec 2 → ℝ) (i : Fin 2) (x : Vec 2) : ℝ :=
  (fderiv ℝ u x) (basisVec i)

/-- Smooth planar cutoff integration by parts. The scalar cutoff is only Lipschitz;
the weak-gradient representative is the one proved above. -/
theorem lipschitz_transport_ibp_smooth {φ u w : Vec 2 → ℝ} {C : ℝ≥0}
    (hφ : LipschitzWith C φ) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (huc : HasCompactSupport u) (hw : ContDiff ℝ (⊤ : ℕ∞) w) :
    (∫ x, φ x * (-(smoothPartial u 0 x * smoothPartial w 1 x) +
      smoothPartial u 1 x * smoothPartial w 0 x)) =
      -((∫ x, lipschitzWeakGradient φ x 0 * (-(u x * smoothPartial w 1 x))) +
        (∫ x, lipschitzWeakGradient φ x 1 * (u x * smoothPartial w 0 x))) := by
  let F : Fin 2 → Vec 2 → ℝ := ![fun x => -(u x * smoothPartial w 1 x),
    fun x => u x * smoothPartial w 0 x]
  have hDw (i : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (smoothPartial w i) :=
    (hw.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
  have hF (i : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (F i) := by
    fin_cases i
    · exact (hu.mul (hDw 1)).neg
    · exact hu.mul (hDw 0)
  have hFc (i : Fin 2) : HasCompactSupport (F i) := by
    fin_cases i
    · exact huc.mul_right.neg
    · exact huc.mul_right
  have hdiv (x : Vec 2) : (∑ i : Fin 2, (fderiv ℝ (F i) x) (basisVec i)) =
      -(smoothPartial u 0 x * smoothPartial w 1 x) +
        smoothPartial u 1 x * smoothPartial w 0 x := by
    have h0 := (((hu.differentiable (by simp)) x).hasFDerivAt.mul
      (((hDw 1).differentiable (by simp)) x).hasFDerivAt).neg
    have h1 := ((hu.differentiable (by simp)) x).hasFDerivAt.mul
      (((hDw 0).differentiable (by simp)) x).hasFDerivAt
    change HasFDerivAt (fun y => -(u y * smoothPartial w 1 y)) _ x at h0
    change HasFDerivAt (fun y => u y * smoothPartial w 0 y) _ x at h1
    simp only [Fin.sum_univ_two, F, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [h0.fderiv, h1.fderiv]
    simp only [neg_apply, add_apply,
      smul_apply, smul_eq_mul]
    unfold smoothPartial
    rw [planar_cross_derivatives_commute hw x]
    ring
  have h := integral_lipschitz_divergence hφ F hF hFc
  simp_rw [hdiv] at h
  simp only [Fin.sum_univ_two, F, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  linarith only [h]

end ASDExplicitGamma.Cold
