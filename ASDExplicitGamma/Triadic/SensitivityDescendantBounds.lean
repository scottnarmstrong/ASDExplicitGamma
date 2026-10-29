module

public import ASDExplicitGamma.Triadic.SensitivityProduct
public import ASDExplicitGamma.Triadic.PlanarDirectionOperations
public import ASDExplicitGamma.Triadic.HilbertHaarCellGeometry

/-! Scale decay of the explicit sensitivity coefficient under cube restriction. -/

@[expose] public section

namespace ASDExplicitGamma.Triadic

open Homogenization MeasureTheory
open scoped ENNReal

private theorem sensitivity_vecL2Norm_memLp_top {μ : Measure (Vec 2)}
    [IsFiniteMeasure μ]
    (f : Vec 2 → Fin 2 → ℝ)
    (hf : ∀ i, MemLp (fun x => f x i) ⊤ μ) :
    MemLp (fun x => planarEuclideanNorm (f x)) ⊤ μ := by
  let C : ℝ := ∑ i : Fin 2, lpNorm (fun x => f x i) ⊤ μ
  have hC : 0 ≤ C := by
    dsimp [C]
    exact Finset.sum_nonneg fun i _ => lpNorm_nonneg
  have hbound : ∀ᵐ x ∂μ, ‖planarEuclideanNorm (f x)‖ ≤ C := by
    have h0 := ae_le_lpNorm_exponent_top (hf 0)
    have h1 := ae_le_lpNorm_exponent_top (hf 1)
    filter_upwards [h0, h1] with x hx0 hx1
    have hL0 : 0 ≤ lpNorm (fun y => f y 0) ⊤ μ := lpNorm_nonneg
    have hL1 : 0 ≤ lpNorm (fun y => f y 1) ⊤ μ := lpNorm_nonneg
    have ha0 : |f x 0| ≤ lpNorm (fun y => f y 0) ⊤ μ := by
      simpa [Real.norm_eq_abs] using hx0
    have ha1 : |f x 1| ≤ lpNorm (fun y => f y 1) ⊤ μ := by
      simpa [Real.norm_eq_abs] using hx1
    have hs0 : (f x 0) ^ 2 ≤ (lpNorm (fun y => f y 0) ⊤ μ) ^ 2 := by
      have hs := (sq_le_sq₀ (abs_nonneg _) hL0).2 ha0
      simpa [sq_abs] using hs
    have hs1 : (f x 1) ^ 2 ≤ (lpNorm (fun y => f y 1) ⊤ μ) ^ 2 := by
      have hs := (sq_le_sq₀ (abs_nonneg _) hL1).2 ha1
      simpa [sq_abs] using hs
    have hsum : (planarEuclideanNorm (f x)) ^ 2 ≤ C ^ 2 := by
      unfold planarEuclideanNorm
      rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (f x i))]
      dsimp [C]
      simp only [Fin.sum_univ_two]
      nlinarith [hs0, hs1, mul_nonneg hL0 hL1]
    have hroot : planarEuclideanNorm (f x) ≤ C :=
      (sq_le_sq₀ (Real.sqrt_nonneg _) hC).mp hsum
    simpa [Real.norm_eq_abs, planarEuclideanNorm,
      abs_of_nonneg (Real.sqrt_nonneg _)] using hroot
  have hmeas : AEStronglyMeasurable
      (fun x => planarEuclideanNorm (f x)) μ := by
    apply Real.continuous_sqrt.comp_aestronglyMeasurable
    convert Finset.aestronglyMeasurable_sum Finset.univ
      (fun i _ => (hf i).aestronglyMeasurable.pow 2) using 1
    funext x
    simp
  exact MemLp.of_bound hmeas C hbound

private theorem sensitivity_planarNorm_memLp_top (Q : TriadicCube 2)
    (b : PlanarW1Infinity Q) :
    MemLp (fun x => planarEuclideanNorm (planarW1Value b x)) ⊤
      (normalizedCubeMeasure Q) := by
  exact sensitivity_vecL2Norm_memLp_top _ fun i => b.component_memLp_top i

private theorem sensitivity_planarHessianNorm_memLp_top (Q : TriadicCube 2)
    (b : PlanarW1Infinity Q) :
    MemLp (fun x => planarFrobeniusNorm (planarW1Derivative b x)) ⊤
      (normalizedCubeMeasure Q) := by
  have hrow : ∀ i : Fin 2,
      MemLp (fun x => planarEuclideanNorm (fun j => planarW1Derivative b x i j))
        ⊤ (normalizedCubeMeasure Q) := by
    intro i
    exact sensitivity_vecL2Norm_memLp_top _ fun j => b.derivative_memLp_top i j
  have hout := sensitivity_vecL2Norm_memLp_top
    (fun x i => planarEuclideanNorm (fun j => planarW1Derivative b x i j)) hrow
  convert hout using 1
  funext x
  unfold planarFrobeniusNorm planarEuclideanNorm planarW1Derivative
  simp only [Fin.sum_univ_two]
  have h0 : (Real.sqrt ((b.component 0).grad x 0 ^ 2 +
      (b.component 0).grad x 1 ^ 2)) ^ 2 =
      (b.component 0).grad x 0 ^ 2 + (b.component 0).grad x 1 ^ 2 := by
    rw [Real.sq_sqrt]
    positivity
  have h1 : (Real.sqrt ((b.component 1).grad x 0 ^ 2 +
      (b.component 1).grad x 1 ^ 2)) ^ 2 =
      (b.component 1).grad x 0 ^ 2 + (b.component 1).grad x 1 ^ 2 := by
    rw [Real.sq_sqrt]
    positivity
  rw [h0, h1]

private theorem planarW1ValueLInf_restrict_le {Q R : TriadicCube 2} {j : ℕ}
    (b : PlanarW1Infinity Q) (hR : R ∈ descendantsAtDepth Q j) :
    planarW1ValueLInf (b.restrict hR) ≤ planarW1ValueLInf b := by
  have hparent : ∀ᵐ x ∂normalizedCubeMeasure Q,
      planarEuclideanNorm (planarW1Value b x) ≤ planarW1ValueLInf b := by
    have h := ae_le_lpNorm_exponent_top (sensitivity_planarNorm_memLp_top Q b)
    filter_upwards [h] with x hx
    have hnonneg : 0 ≤ planarEuclideanNorm (planarW1Value b x) := Real.sqrt_nonneg _
    change ‖planarEuclideanNorm (planarW1Value b x)‖ ≤ _ at hx
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg] at hx
    simpa [planarW1ValueLInf, lpNorm] using hx
  have hlocal := hilbert_ae_descendant hR hparent
  refine planarW1ValueLInf_le_of_bound (b.restrict hR)
    (G := planarW1ValueLInf b) ?_ ?_
  · unfold planarW1ValueLInf
    exact ENNReal.toReal_nonneg
  filter_upwards [hlocal] with x hx
  change planarEuclideanNorm (planarW1Value b x) ≤ planarW1ValueLInf b
  exact hx

private theorem planarW1DerivativeLInf_restrict_le {Q R : TriadicCube 2} {j : ℕ}
    (b : PlanarW1Infinity Q) (hR : R ∈ descendantsAtDepth Q j) :
    planarW1DerivativeFrobeniusLInf (b.restrict hR) ≤
      planarW1DerivativeFrobeniusLInf b := by
  have hparent : ∀ᵐ x ∂normalizedCubeMeasure Q,
      planarFrobeniusNorm (planarW1Derivative b x) ≤
        planarW1DerivativeFrobeniusLInf b := by
    have h := ae_le_lpNorm_exponent_top (sensitivity_planarHessianNorm_memLp_top Q b)
    filter_upwards [h] with x hx
    have hnonneg : 0 ≤ planarFrobeniusNorm (planarW1Derivative b x) :=
      Real.sqrt_nonneg _
    change ‖planarFrobeniusNorm (planarW1Derivative b x)‖ ≤ _ at hx
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg] at hx
    simpa [planarW1DerivativeFrobeniusLInf, lpNorm] using hx
  have hlocal := hilbert_ae_descendant hR hparent
  refine planarW1DerivativeFrobeniusLInf_le_of_bound (b.restrict hR)
    (H := planarW1DerivativeFrobeniusLInf b) ?_ ?_
  · unfold planarW1DerivativeFrobeniusLInf
    exact ENNReal.toReal_nonneg
  filter_upwards [hlocal] with x hx
  change planarFrobeniusNorm (planarW1Derivative b x) ≤
    planarW1DerivativeFrobeniusLInf b
  exact hx

private theorem planarGradientLInf_restrict_le {Q R : TriadicCube 2} {j : ℕ}
    (h : PlanarW2Infinity Q) (hR : R ∈ descendantsAtDepth Q j) :
    planarGradientLInf (h.restrict hR) ≤ planarGradientLInf h := by
  exact planarW1ValueLInf_restrict_le h.gradient hR

private theorem planarHessianLInf_restrict_le {Q R : TriadicCube 2} {j : ℕ}
    (h : PlanarW2Infinity Q) (hR : R ∈ descendantsAtDepth Q j) :
    planarHessianFrobeniusLInf (h.restrict hR) ≤
      planarHessianFrobeniusLInf h := by
  exact planarW1DerivativeLInf_restrict_le h.gradient hR

/-- On a depth-j descendant, the source sensitivity coefficient loses one
factor `3^j` from the cube scale. -/
theorem sensitivityDsharp_descendant_le {Q R : TriadicCube 2} {j : ℕ}
    (h : PlanarW2Infinity Q) (hR : R ∈ descendantsAtDepth Q j) :
    sensitivityDsharp R (h.restrict hR) ≤ (3 : ℝ) ^ (-(j : ℤ)) *
      sensitivityDsharp Q h := by
  have hscale : cubeScaleFactor R = cubeScaleFactor Q / (3 : ℝ) ^ j :=
    cubeScaleFactor_descendant_eq_div_pow hR
  have hscaleQ : 0 ≤ cubeScaleFactor Q := (cubeScaleFactor_pos' Q).le
  have hscaleR : 0 ≤ cubeScaleFactor R := (cubeScaleFactor_pos' R).le
  have hc : 0 ≤ sensitivityKappaH := by
    unfold sensitivityKappaH planarC0 planarC1
    positivity
  have hg : 0 ≤ planarGradientLInf h := by
    unfold planarGradientLInf planarW1ValueLInf
    exact ENNReal.toReal_nonneg
  have hh : 0 ≤ planarHessianFrobeniusLInf h := by
    unfold planarHessianFrobeniusLInf planarW1DerivativeFrobeniusLInf
    exact ENNReal.toReal_nonneg
  have hgrad := planarGradientLInf_restrict_le h hR
  have hhess := planarHessianLInf_restrict_le h hR
  have hD1 : sensitivityD1 R (h.restrict hR) ≤
      (3 : ℝ) ^ (-(j : ℤ)) * sensitivityD1 Q h := by
    rw [sensitivityD1, sensitivityD1, hscale]
    have hpowpos : 0 < (3 : ℝ) ^ j := by positivity
    have hpowone : 1 ≤ (3 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    have hpow : (3 : ℝ) ^ (-(j : ℤ)) = ((3 : ℝ) ^ j)⁻¹ := by
      rw [zpow_neg, zpow_natCast]
    rw [hpow]
    have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    calc
      (cubeScaleFactor Q / (3 : ℝ) ^ j) * Real.sqrt 2 *
          planarGradientLInf (h.restrict hR) ≤
        (cubeScaleFactor Q / (3 : ℝ) ^ j) * Real.sqrt 2 * planarGradientLInf h :=
          mul_le_mul_of_nonneg_left hgrad (mul_nonneg (div_nonneg hscaleQ hpowpos.le) hsqrt)
      _ = ((3 : ℝ) ^ j)⁻¹ *
          (cubeScaleFactor Q * Real.sqrt 2 * planarGradientLInf h) := by
            rw [div_eq_mul_inv]
            ring
  have hD2 : sensitivityD2 R (h.restrict hR) ≤
      (3 : ℝ) ^ (-(j : ℤ)) * sensitivityD2 Q h := by
    rw [sensitivityD2, sensitivityD2, hscale]
    have hpowpos : 0 < (3 : ℝ) ^ j := by positivity
    have hpowone : 1 ≤ (3 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    have hpow : (3 : ℝ) ^ (-(j : ℤ)) = ((3 : ℝ) ^ j)⁻¹ := by
      rw [zpow_neg, zpow_natCast]
    rw [hpow]
    have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    have hpownonneg : 0 ≤ (3 : ℝ) ^ j := hpowpos.le
    have hinv := (inv_le_one₀ hpowpos).2 hpowone
    have hnonneg : 0 ≤ ((3 : ℝ) ^ j)⁻¹ := inv_nonneg.mpr hpowpos.le
    have hfactor : ((3 : ℝ) ^ j)⁻¹ ^ 2 ≤ ((3 : ℝ) ^ j)⁻¹ := by
      calc
        ((3 : ℝ) ^ j)⁻¹ ^ 2 = ((3 : ℝ) ^ j)⁻¹ * ((3 : ℝ) ^ j)⁻¹ := by ring
        _ ≤ 1 * ((3 : ℝ) ^ j)⁻¹ := mul_le_mul_of_nonneg_right hinv hnonneg
        _ = ((3 : ℝ) ^ j)⁻¹ := by ring
    calc
      (cubeScaleFactor Q / (3 : ℝ) ^ j) ^ 2 * Real.sqrt 2 *
          planarHessianFrobeniusLInf (h.restrict hR) ≤
        (cubeScaleFactor Q / (3 : ℝ) ^ j) ^ 2 * Real.sqrt 2 *
          planarHessianFrobeniusLInf h :=
            mul_le_mul_of_nonneg_left hhess (mul_nonneg (sq_nonneg _) hsqrt)
      _ ≤ ((3 : ℝ) ^ j)⁻¹ *
          (cubeScaleFactor Q ^ 2 * Real.sqrt 2 *
            planarHessianFrobeniusLInf h) := by
        rw [div_pow]
        have hsquare : ((3 : ℝ) ^ j)⁻¹ ^ 2 *
            (cubeScaleFactor Q ^ 2 * Real.sqrt 2 *
              planarHessianFrobeniusLInf h) ≤
            ((3 : ℝ) ^ j)⁻¹ *
              (cubeScaleFactor Q ^ 2 * Real.sqrt 2 *
                planarHessianFrobeniusLInf h) :=
          mul_le_mul_of_nonneg_right hfactor
            (mul_nonneg (mul_nonneg (sq_nonneg _) hsqrt) hh)
        calc
          cubeScaleFactor Q ^ 2 / ((3 : ℝ) ^ j) ^ 2 * Real.sqrt 2 *
              planarHessianFrobeniusLInf h =
            ((3 : ℝ) ^ j)⁻¹ ^ 2 *
              (cubeScaleFactor Q ^ 2 * Real.sqrt 2 *
                planarHessianFrobeniusLInf h) := by rw [div_eq_mul_inv]; ring
          _ ≤ _ := hsquare
  unfold sensitivityDsharp
  calc
    sensitivityD1 R (h.restrict hR) + sensitivityKappaH *
        sensitivityD2 R (h.restrict hR) ≤
      (3 : ℝ) ^ (-(j : ℤ)) * sensitivityD1 Q h +
        sensitivityKappaH * ((3 : ℝ) ^ (-(j : ℤ)) * sensitivityD2 Q h) :=
          add_le_add hD1 (mul_le_mul_of_nonneg_left hD2 hc)
    _ = (3 : ℝ) ^ (-(j : ℤ)) *
        (sensitivityD1 Q h + sensitivityKappaH * sensitivityD2 Q h) := by ring

end ASDExplicitGamma.Triadic
