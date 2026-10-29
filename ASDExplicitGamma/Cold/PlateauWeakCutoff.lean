module

public import ASDExplicitGamma.Cold.LipschitzWeakGradient

/-! # The zero-extended plateau as an actual weak Sobolev cutoff -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Homogenization
open scoped BigOperators ENNReal NNReal

namespace ASDExplicitGamma.Cold

/-- The continuous zero extension of the source plateau from the closed square. -/
def plateauZeroExtension (x : Vec 2) : ℝ := max (plateauCutoff x) 0

/-- This extension agrees with the source cutoff at every point of the square. -/
theorem plateauZeroExtension_eq {x : Vec 2} (hx : x ∈ plateauUnitSquare) :
    plateauZeroExtension x = plateauCutoff x :=
  max_eq_left (plateauCutoff_nonneg hx)

/-- Zero extension preserves the source Lipschitz constant. -/
theorem lipschitzWith_plateauZeroExtension : LipschitzWith (48 / 7) plateauZeroExtension :=
  lipschitzWith_plateauCutoff.max_const 0

/-- The zero extension is nonnegative on the entire plane. -/
theorem plateauZeroExtension_nonneg (x : Vec 2) : 0 ≤ plateauZeroExtension x :=
  le_max_right _ _

/-- The global value bound used in Sobolev multiplication. -/
theorem norm_plateauZeroExtension_le (x : Vec 2) : ‖plateauZeroExtension x‖ ≤ 12 / 7 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (plateauZeroExtension_nonneg x)]
  exact max_le (plateauCutoff_le x) (by norm_num)

/-- The extension vanishes off the source square. -/
theorem plateauZeroExtension_eq_zero_of_not_mem {x : Vec 2} (hx : x ∉ plateauUnitSquare) :
    plateauZeroExtension x = 0 := by
  have hneg : plateauCutoff x < 0 := by
    apply lt_of_not_ge
    intro h
    exact hx (plateauCutoff_superlevel_subset (s := 0) (by norm_num) (by norm_num) h)
  exact max_eq_right hneg.le

/-- The sup spatial norm is bounded by the Euclidean norm, in the explicit planar carrier. -/
theorem planar_sup_norm_le_sqrt_sum_sq (v : Vec 2) :
    ‖v‖ ≤ Real.sqrt (∑ i : Fin 2, v i ^ 2) := by
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
  intro i
  apply Real.le_sqrt_of_sq_le
  rw [Real.norm_eq_abs, sq_abs]
  exact Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)

/-- Evaluation of a planar linear functional in the coordinate carrier. -/
theorem planar_clm_apply_eq_sum (L : Vec 2 →L[ℝ] ℝ) (v : Vec 2) :
    L v = ∑ i : Fin 2, L (basisVec i) * v i := by
  have he : v = ∑ i : Fin 2, v i • basisVec i := by
    ext i
    simp [basisVec, Pi.single_apply]
  conv_lhs => rw [he, map_sum]
  simp only [map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A global Lipschitz bound controls the actual weak-gradient pairing in Euclidean norm. -/
theorem lipschitzWeakGradient_ae_pairing {f : Vec 2 → ℝ} {C : ℝ≥0} (hf : LipschitzWith C f) :
    ∀ᵐ x ∂volume, ∀ v : Vec 2,
      |∑ i : Fin 2, lipschitzWeakGradient f x i * v i| ≤
        (C : ℝ) * Real.sqrt (∑ i : Fin 2, v i ^ 2) := by
  filter_upwards [lipschitzWeakGradient_ae_eq_fderiv hf] with x hx
  intro v
  simp_rw [hx]
  rw [← planar_clm_apply_eq_sum]
  calc
    _ = ‖(fderiv ℝ f x) v‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖fderiv ℝ f x‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (C : ℝ) * ‖v‖ := mul_le_mul_of_nonneg_right
      (norm_fderiv_le_of_lipschitz ℝ hf) (norm_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left (planar_sup_norm_le_sqrt_sum_sq v) C.coe_nonneg

/-- The squared Euclidean weak-gradient bound follows from the actual pairing bound. -/
theorem lipschitzWeakGradient_ae_sq_bound {f : Vec 2 → ℝ} {C : ℝ≥0} (hf : LipschitzWith C f) :
    ∀ᵐ x ∂volume, (∑ i : Fin 2, lipschitzWeakGradient f x i ^ 2) ≤ (C : ℝ) ^ 2 := by
  filter_upwards [lipschitzWeakGradient_ae_pairing hf] with x hx
  have h := hx (lipschitzWeakGradient f x)
  have hn : 0 ≤ ∑ i : Fin 2, lipschitzWeakGradient f x i ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  simp only [← sq, abs_of_nonneg hn] at h
  have hs := Real.sq_sqrt hn
  have hroot : Real.sqrt (∑ i : Fin 2, lipschitzWeakGradient f x i ^ 2) ≤ C := by
    nlinarith only [h, hs, Real.sqrt_nonneg (∑ i : Fin 2, lipschitzWeakGradient f x i ^ 2), C.coe_nonneg]
  nlinarith only [hs, pow_le_pow_left₀ (Real.sqrt_nonneg _) hroot 2]

end ASDExplicitGamma.Cold
