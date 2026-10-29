module

public import ASDExplicitGamma.Scalar.CombineCross

/-! Pathwise bound of the flat-leg cross term on Wick truncations, with the AM-GM split. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
open Algsuperdiff.Section3 ASDExplicitGamma.Native ASDExplicitGamma.Inverse Filter
open scoped InnerProductSpace BigOperators ENNReal Topology

attribute [local irreducible] Homogenization.descendantsAtDepth

noncomputable section

/-- AM-GM in the form used for the Cauchy-Schwarz over `Ω`. -/
theorem amgm_split {s x y t c : ℝ} (hs : 0 ≤ s) (hx : 0 ≤ x) (hy : 0 ≤ y) (ht : 0 < t)
    (hc : 0 ≤ c) :
    2 * (s * (c * (Real.sqrt x * Real.sqrt y))) ≤
      t * (c * (s ^ 2 * x)) + c / t * y := by
  have hxx : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
  have hyy : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy
  set u := Real.sqrt x
  set v := Real.sqrt y
  have h1 : 0 ≤ c * (t * s * u - v) ^ 2 / t := by positivity
  have h2 : c * (t * s * u - v) ^ 2 / t =
      t * (c * (s ^ 2 * u ^ 2)) + c / t * v ^ 2 - 2 * (s * (c * (u * v))) := by
    field_simp
    ring
  rw [hxx, hyy] at h2
  linarith

namespace Cfg''

section Flat

variable (M : ABKModel 2) (h : ℝ) (m : ℤ) {a b c d : ℝ} (hab : a < b) (hcd : c < d)
  (hQ : openCubeSet (originCube 2 (m + 129)) ⊆ openRectangle a b c d) (e : Vec 2)

local notation "CC" => finalCfg M h m hab hcd hQ e

include hQ in
theorem crossTruncR_le (ω : Cutoff.CutoffSample 2) (n : ℕ) (x : Fin n → ℝ) :
    (CC).crossTruncR m ω n x ≤ ((((CC).σ ^ 2)⁻¹ : ℝ)) * ((141 / 100 : ℝ) *
      ((volume (openCubeSet (originCube 2 (m + 129)))).toReal *
        (Real.sqrt (bnew M m (originCube 2 (m + 129)) ω * lemmaVTiledPositiveEnergy
            (originCube 2 (m + 129)) 134 (flatField (originCube 2 (m + 129)) hab hcd e m ω)) *
          Real.sqrt (bnew M m (originCube 2 (m + 129)) ω *
            (tiledPositiveEnergy (originCube 2 (m + 129)) 134
              (psdDefectSource ((CC).BFoR ((CC).old m ω) n) x) +
             tiledPositiveEnergy (originCube 2 (m + 129)) 134
              (psdDefectSource ((CC).BGoR ((CC).old m ω) n) x)))))) := by
  classical
  obtain ⟨ell, hK⟩ := exists_originCube_containing_compact (closedRectangle a b c d)
    (closedRectangle_isCompact a b c d)
  have hFa := flatField_memL2 m hab hcd hQ e ω
  have hadm := flatCellAdm m hab hcd hQ e ω
  have main := (CC).cross_trunc_le m M rfl rfl ell hK ω n x hFa hadm
    (fluxSource (originCube 2 (m + 129)) hFa) (fluxSource_mem _ hFa)
    (fluxSource_inner _ hFa)
    (WithLp.toLp 2 (fluxSource (originCube 2 (m + 129)) hFa, (0 : (CC).Xs))) rfl
  have haR := aR_eq M h m hab hcd hQ e ω
  unfold crossTruncR
  rw [haR, map_smul]
  rw [show ∀ (c : ℝ) (u v : (CC).Pr), ⟪u, c • v⟫_ℝ = c * ⟪u, v⟫_ℝ from
    fun c u v => real_inner_smul_right u v c]
  exact mul_le_mul_of_nonneg_left main (inv_nonneg.2 (sq_nonneg _))

include hQ in
theorem crossTruncR_amgm (ω : Cutoff.CutoffSample 2) (n : ℕ) (x : Fin n → ℝ) {t : ℝ}
    (ht : 0 < t) :
    2 * (CC).crossTruncR m ω n x ≤
      t * ((141 / 100 : ℝ) * ((volume (openCubeSet (originCube 2 (m + 129)))).toReal *
        (((((CC).σ ^ 2)⁻¹ : ℝ)) ^ 2 * (bnew M m (originCube 2 (m + 129)) ω *
          lemmaVTiledPositiveEnergy (originCube 2 (m + 129)) 134
            (flatField (originCube 2 (m + 129)) hab hcd e m ω))))) +
      (141 / 100 : ℝ) / t * ((volume (openCubeSet (originCube 2 (m + 129)))).toReal *
        (bnew M m (originCube 2 (m + 129)) ω *
          (tiledPositiveEnergy (originCube 2 (m + 129)) 134
            (psdDefectSource ((CC).BFoR ((CC).old m ω) n) x) +
           tiledPositiveEnergy (originCube 2 (m + 129)) 134
            (psdDefectSource ((CC).BGoR ((CC).old m ω) n) x)))) := by
  have hB := bnew_nonneg M m (originCube 2 (m + 129)) ω
  have hP := lemmaVTiledPositiveEnergy_nonneg (originCube 2 (m + 129)) 134
    (flatField (originCube 2 (m + 129)) hab hcd e m ω)
  have hS : 0 ≤ tiledPositiveEnergy (originCube 2 (m + 129)) 134
      (psdDefectSource ((CC).BFoR ((CC).old m ω) n) x) +
      tiledPositiveEnergy (originCube 2 (m + 129)) 134
      (psdDefectSource ((CC).BGoR ((CC).old m ω) n) x) := by
    unfold tiledPositiveEnergy
    exact add_nonneg (lemmaVTiledPositiveEnergy_nonneg _ _ _) (lemmaVTiledPositiveEnergy_nonneg _ _ _)
  have hvol : 0 ≤ (volume (openCubeSet (originCube 2 (m + 129)))).toReal := ENNReal.toReal_nonneg
  have h1 := crossTruncR_le M h m hab hcd hQ e ω n x
  have h2 := amgm_split (s := (((CC).σ ^ 2)⁻¹ : ℝ))
    (x := bnew M m (originCube 2 (m + 129)) ω * lemmaVTiledPositiveEnergy
      (originCube 2 (m + 129)) 134 (flatField (originCube 2 (m + 129)) hab hcd e m ω))
    (y := bnew M m (originCube 2 (m + 129)) ω *
      (tiledPositiveEnergy (originCube 2 (m + 129)) 134
        (psdDefectSource ((CC).BFoR ((CC).old m ω) n) x) +
       tiledPositiveEnergy (originCube 2 (m + 129)) 134
        (psdDefectSource ((CC).BGoR ((CC).old m ω) n) x)))
    (inv_nonneg.2 (sq_nonneg _)) (mul_nonneg hB hP) (mul_nonneg hB hS) ht
    (show (0 : ℝ) ≤ (141 / 100 : ℝ) * (volume (openCubeSet (originCube 2 (m + 129)))).toReal by
      positivity)
  refine le_trans (by linarith [h1]) (h2.trans (le_of_eq ?_))
  ring

end Flat

end Cfg''

end

end ASDExplicitGamma.Scalar
