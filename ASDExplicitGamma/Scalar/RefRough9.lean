module

public import ASDExplicitGamma.Scalar.RefRough8
public import ASDExplicitGamma.Scalar.RefBudget3

/-! **Provable rough bound** for the defect budget: pathwise
`Λ ≤ amp² A² ((44/25) B* + 1)⁴` and hence `‖Λ‖_{L^{128/127}} ≤ amp² R`,
`R = A² ((44/25) b + 1)⁴`, `b = 14103/10000`. No `α⁻¹`, no hypotheses beyond the standing ones. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
  ASDExplicitGamma.Native
open Algsuperdiff.Section3
open scoped BigOperators ENNReal

attribute [local irreducible] Homogenization.descendantsAtDepth

noncomputable section

section Rough

variable (M : ABKModel 2) (h : ℝ) (m : ℤ) {a b c d : ℝ} (hab : a < b) (hcd : c < d)
  (hQ : openCubeSet (originCube 2 (m + 129)) ⊆ openRectangle a b c d) (e : Vec 2)

local notation "CC" => finalCfg M h m hab hcd hQ e

/-- The explicit rough constant. -/
def roughR : ℝ := defectA ^ 2 * ((44 / 25 : ℝ) * (14103 / 10000) + 1) ^ 4

include h hab hcd hQ

theorem Lam_rough_pathwise (he2 : vecNormSq e = 1) (ell : ℤ)
    (hK : closedRectangle a b c d ⊆ openCubeSet (originCube 2 ell)) (ω : Cutoff.CutoffSample 2)
    (n : ℕ) :
    (CC).LamFR n (olderField (closedRectangle a b c d) m ω) +
      (CC).LamGR n (olderField (closedRectangle a b c d) m ω) ≤
    (CC).amp ^ 2 * (defectA ^ 2 *
      ((44 / 25 : ℝ) * bhist M m (originCube 2 (m + 129)) 134 ω + 1) ^ 4) := by
  let C := finalCfg M h m hab hcd hQ e
  let old := olderField (closedRectangle a b c d) m ω
  have hrest : C.Rest old = oldCutoffSkewCoefficient m C.Q ω :=
    rest_old_eq M (closedRectangle a b c d) ell m hK C.Q C.hQcl ω
  have hB : ∀ U ∈ descendantsAtDepth C.Q 134, lemmaVInverseHistory U
      (responseFramePlanarCoefficientField C.ν C.σ (C.Rest old)) ((3 : ℝ) ^ (1 / 4 : ℝ)) ≤
        bhist M m C.Q 134 ω := by
    intro U hU
    rw [hrest]
    exact hist_le_Bhist M m C.Q U hU ω
  have hB0 := Bhist_nonneg M m C.Q 134 ω
  have hΛ0 := add_nonneg (C.LamFR_nonneg n old) (C.LamGR_nonneg n old)
  have h1 := C.lam_splitR n old
  have hf := C.forced_rough hQ (mesh' m) he2 old n hB0 hB
  have hTr := T_rough M h m hab hcd hQ e he2 ell hK ω
  have hin := inner_pathwise M h m hab hcd hQ e ell hK ω n
  have hT0 : 0 ≤ dirTiledBot M m C.Q e ω :=
    le_of_le_of_eq (add_nonneg (lemmaVTiledWeakEnergy_nonneg _ _ _)
      (lemmaVTiledWeakEnergy_nonneg _ _ _)) (final_flat_budget M h m hab hcd hQ e ell hK ω)
  have hA0 : 0 ≤ defectA := by unfold defectA; positivity
  have hT2 : dirTiledBot M m C.Q e ω ≤ ((44 / 25 : ℝ) * bhist M m C.Q 134 ω + 1) ^ 2 := by
    have hTr' : Real.sqrt (dirTiledBot M m C.Q e ω) ≤
        (44 / 25 : ℝ) * bhist M m C.Q 134 ω + 1 := hTr
    have := pow_le_pow_left₀ (Real.sqrt_nonneg _) hTr' 2
    rwa [Real.sq_sqrt hT0] at this
  have hinner : Real.sqrt (C.innerLam n old) ≤ (44 / 25 : ℝ) * bhist M m C.Q 134 ω *
      (defectA * |C.amp|) * ((44 / 25 : ℝ) * bhist M m C.Q 134 ω + 1) := by
    have hbd : C.innerLam n old ≤ ((44 / 25 : ℝ) * bhist M m C.Q 134 ω *
        (defectA * |C.amp|) * ((44 / 25 : ℝ) * bhist M m C.Q 134 ω + 1)) ^ 2 := by
      refine hin.trans ?_
      have hA : 0 ≤ ((44 / 25 : ℝ) * bhist M m C.Q 134 ω) ^ 2 * (defectA ^ 2 * C.amp ^ 2) := by
        positivity
      calc _ ≤ ((44 / 25 : ℝ) * bhist M m C.Q 134 ω) ^ 2 * (defectA ^ 2 * C.amp ^ 2) *
            ((44 / 25 : ℝ) * bhist M m C.Q 134 ω + 1) ^ 2 := mul_le_mul_of_nonneg_left hT2 hA
        _ = _ := by
          simp only [mul_pow, sq_abs] <;> ring
    have hnn : 0 ≤ (44 / 25 : ℝ) * bhist M m C.Q 134 ω * (defectA * |C.amp|) *
        ((44 / 25 : ℝ) * bhist M m C.Q 134 ω + 1) := by positivity
    calc _ ≤ Real.sqrt (_ ^ 2) := Real.sqrt_le_sqrt hbd
      _ = _ := Real.sqrt_sq hnn
  have h4 : Real.sqrt (C.LamFR n old + C.LamGR n old) ≤
      defectA * |C.amp| * ((44 / 25 : ℝ) * bhist M m C.Q 134 ω + 1) ^ 2 := by
    refine h1.trans ((add_le_add hf hinner).trans (le_of_eq ?_))
    ring
  have hnn2 : 0 ≤ defectA * |C.amp| * ((44 / 25 : ℝ) * bhist M m C.Q 134 ω + 1) ^ 2 := by
    positivity
  calc C.LamFR n old + C.LamGR n old = Real.sqrt (C.LamFR n old + C.LamGR n old) ^ 2 :=
        (Real.sq_sqrt hΛ0).symm
    _ ≤ (defectA * |C.amp| * ((44 / 25 : ℝ) * bhist M m C.Q 134 ω + 1) ^ 2) ^ 2 :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) h4 2
    _ = C.amp ^ 2 * (defectA ^ 2 *
        ((44 / 25 : ℝ) * bhist M m C.Q 134 ω + 1) ^ 4) := by
        simp only [mul_pow, sq_abs] <;> ring

end Rough

end

end ASDExplicitGamma.Scalar
