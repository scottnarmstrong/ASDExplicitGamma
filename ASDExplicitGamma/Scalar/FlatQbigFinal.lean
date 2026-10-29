module

public import ASDExplicitGamma.Scalar.FlatQbigLaw
public import ASDExplicitGamma.Scalar.FlatSourceQ3ActualBank
public import ASDExplicitGamma.Scalar.DefectNewBank
public import ASDExplicitGamma.Scalar.DefectFinalPhys
public import ASDExplicitGamma.Scalar.RefQuart

/-! Q_big flat successor: the expectation of the pathwise flat majorant
`σ⁻⁴ · B* · PE(F_flat)` on the single parent `Q_big = originCube 2 (m+129)` against the NEW bank. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Homogenization Filter
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped ENNReal Topology

namespace ASDExplicitGamma.Scalar

noncomputable section

/-- Uniform scale arithmetic for the tiled cap. -/
theorem tile_raw_cap (Q : TriadicCube 2) (L : {l : ℝ // 0 < l}) (amp : ℝ)
    (hscale : tileSide Q ≤ L.1 / 27) :
    (3 / 2 : ℝ) * amp ^ 4 + (467 / 1000 : ℝ) ^ 2 * tileSide Q ^ 2 *
        ((936 / 5 : ℝ) * amp ^ 4 / L.1 ^ 2) ≤ (1557 / 1000 : ℝ) * amp ^ 4 := by
  have hratio : tileSide Q / L.1 ≤ (1 / 27 : ℝ) :=
    (div_le_iff₀ L.2).2 (by nlinarith [hscale])
  have hratio0 : 0 ≤ tileSide Q / L.1 := div_nonneg (tileSide_pos Q).le L.2.le
  have hratio2 : (tileSide Q / L.1) ^ 2 ≤ (1 / 27 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hratio0 hratio 2
  have hfactor : (3 / 2 : ℝ) + (467 / 1000 : ℝ) ^ 2 * (936 / 5 : ℝ) *
      (tileSide Q / L.1) ^ 2 ≤ (1557 / 1000 : ℝ) := by
    calc
      _ ≤ (3 / 2 : ℝ) + (467 / 1000 : ℝ) ^ 2 * (936 / 5 : ℝ) * (1 / 27 : ℝ) ^ 2 := by
        gcongr
      _ ≤ _ := by norm_num
  have hamp4 : 0 ≤ amp ^ 4 := by positivity
  have hrewrite : (3 / 2 : ℝ) * amp ^ 4 + (467 / 1000 : ℝ) ^ 2 * tileSide Q ^ 2 *
        ((936 / 5 : ℝ) * amp ^ 4 / L.1 ^ 2) =
      ((3 / 2 : ℝ) + (467 / 1000 : ℝ) ^ 2 * (936 / 5 : ℝ) *
        (tileSide Q / L.1) ^ 2) * amp ^ 4 := by
    field_simp [ne_of_gt L.2]
  rw [hrewrite]
  exact mul_le_mul_of_nonneg_right hfactor hamp4

theorem bigTileSide_le (m : ℤ) :
    tileSide (originCube 2 (m + 129)) ≤ (q3ModelLength (m + 1)).1 / 27 := by
  have hc : cubeScaleFactor (originCube 2 (m + 129)) = (3 : ℝ) ^ (m + 129) := by
    simp [cubeScaleFactor, originCube]
  have hL : (q3ModelLength (m + 1)).1 = (3 : ℝ) ^ (m + 1) := rfl
  have h1 : (3 : ℝ) ^ (m + 129) = (3 : ℝ) ^ (m + 1) * 3 ^ 128 := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num)]
    congr 1
    push_cast
    ring
  unfold tileSide
  rw [hc, hL, h1]
  have hX : 0 < (3 : ℝ) ^ (m + 1) := zpow_pos (by norm_num) _
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  have h134 : (3 : ℝ) ^ 134 = 3 ^ 128 * 729 := by norm_num
  rw [h134]
  have hp : 0 < (3 : ℝ) ^ (m + 1) * 3 ^ 128 := by positivity
  nlinarith

section Final

variable (M : ABKModel 2) (h : ℝ) (m : ℤ) {a b c d : ℝ} (hab : a < b) (hcd : c < d)
  (hQ : openCubeSet (originCube 2 (m + 129)) ⊆ openRectangle a b c d) (e : Vec 2)

local notation "CC" => finalCfg M h m hab hcd hQ e

/-- The flat-leg expectation package for the single parent `Q_big`. -/
theorem flat_expectation_package (hM : PlanarQ3Gaussian M h)
    (hγ : M.gamma ≤ gammaZero) (hpast : ∀ n < m, nativeInductionState M h n)
    (he : Book.Ch02.vecNorm e = 1) :
    let P : Cutoff.CutoffSample 2 → ℝ := fun ω =>
      ((((CC).σ ^ 2)⁻¹ : ℝ) ^ 2) * (bnew M m (originCube 2 (m + 129)) ω *
        lemmaVTiledPositiveEnergy (originCube 2 (m + 129)) 134
          (Cfg''.flatField (originCube 2 (m + 129)) hab hcd e m ω))
    let Fc : ℝ := (1557 / 1000 : ℝ) *
      ((14103 / 10000 : ℝ) + (513 / 500 : ℝ) * (5 / 10 ^ 24 : ℝ))
    0 ≤ Fc ∧ Measurable P ∧ Integrable P (Cutoff.cutoffSampleLaw M).toMeasure ∧
      ∫ ω, P ω ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤ ((CC).amp ^ 2) ^ 2 * Fc := by
  classical
  intro P Fc
  set Q := originCube 2 (m + 129) with hQdef
  set μ := (Cutoff.cutoffSampleLaw M).toMeasure with hμ
  obtain ⟨ell, hK⟩ := exists_originCube_containing_compact (closedRectangle a b c d)
    (closedRectangle_isCompact a b c d)
  have hQcl := hQcl' hab hcd Q hQ
  have hQK : openCubeSet Q ⊆ closedRectangle a b c d := fun x hx => hQcl (subset_closure hx)
  have hQell : openCubeSet Q ⊆ openCubeSet (originCube 2 ell) := hQK.trans hK
  have hQscale : Q.scale = m + 129 := by simp [hQdef, originCube]
  obtain ⟨hB128, hR128⟩ := bank_Bnew M h hM hγ m hpast Q hQscale ell hQell
  have hBm : Measurable (bnew M m Q) := bnew_measurable M ell m Q hQell
  let β := q3ModelAmplitude M h (m + 1)
  let Lm := q3ModelLength (m + 1)
  have hβ : 0 < β := mul_pos hM.1 (Real.rpow_pos_of_pos (by norm_num) _)
  have hσ : 0 < (CC).σ := (CC).hσ
  have hamp : (CC).amp = β / (CC).σ := rfl
  have hscale := bigTileSide_le m
  obtain ⟨hYm, hYlaw1, hYlaw2⟩ := actual_tiled_law Q hab hcd M h hM e (m + 1)
  let Y : Cutoff.CutoffSample 2 → ℝ := fun ω =>
    lemmaVTiledPositiveEnergy Q 134 (Cfg''.flatField Q hab hcd e m ω)
  have hYeq (ω : Cutoff.CutoffSample 2) : Y ω =
      phi' Q 134 (flatSourceQ3ActualWickRepresentative Q hab hcd e (m + 1) ω) :=
    tiled_rot_eq Q 134 _
  have hY0 (ω : Cutoff.CutoffSample 2) : 0 ≤ Y ω := lemmaVTiledPositiveEnergy_nonneg _ _ _
  have hYmeas : Measurable Y := by
    have : Y = fun ω => phi' Q 134
        (flatSourceQ3ActualWickRepresentative Q hab hcd e (m + 1) ω) := funext hYeq
    rw [this]; exact hYm
  have hraw := tile_raw_cap Q Lm β hscale
  have hFexp := fixed_tiled_lintegral_le Q hab hcd hQ M h hM e he (m + 1)
  have hFcap := fixed_tiled_L128 Q hab hcd hQ M h hM e he (m + 1)
  have hF0 : 0 ≤ (1557 / 1000 : ℝ) * β ^ 4 := by positivity
  have hEq1 : ∫⁻ ω, ENNReal.ofReal (Y ω) ∂μ =
      ∫⁻ ω, ENNReal.ofReal (phi' Q 134 (vfix Q hab hcd β Lm e ω))
        ∂standardGaussianInfinitePi := by
    have h1 : ∫⁻ ω, ENNReal.ofReal (Y ω) ∂μ = ∫⁻ ω, ENNReal.ofReal (phi' Q 134
        (flatSourceQ3ActualWickRepresentative Q hab hcd e (m + 1) ω)) ∂μ :=
      lintegral_congr fun ω => by rw [hYeq]
    exact h1.trans hYlaw1
  have hYexp : ∫⁻ ω, ENNReal.ofReal (Y ω) ∂μ ≤ ENNReal.ofReal ((1557 / 1000 : ℝ) * β ^ 4) := by
    rw [hEq1]
    exact hFexp.trans (ENNReal.ofReal_le_ofReal hraw)
  have hYfun : Y = fun ω => phi' Q 134
      (flatSourceQ3ActualWickRepresentative Q hab hcd e (m + 1) ω) := funext hYeq
  have hYL : eLpNorm Y (ENNReal.ofReal (128 / 127 : ℝ)) μ ≤
      ENNReal.ofReal ((513 / 500 : ℝ) * ((1557 / 1000 : ℝ) * β ^ 4)) := by
    calc
      eLpNorm Y (ENNReal.ofReal (128 / 127 : ℝ)) μ =
          eLpNorm (fun ω => phi' Q 134
            (flatSourceQ3ActualWickRepresentative Q hab hcd e (m + 1) ω))
            (ENNReal.ofReal (128 / 127 : ℝ)) μ := by rw [hYfun]
      _ = eLpNorm (fun ω => phi' Q 134 (vfix Q hab hcd β Lm e ω))
            (ENNReal.ofReal (128 / 127 : ℝ)) standardGaussianInfinitePi := hYlaw2
      _ ≤ _ := hFcap.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left hraw (by norm_num)))
  have hYmem : MemLp Y (ENNReal.ofReal (128 / 127 : ℝ)) μ :=
    lt_of_le_of_lt hYL ENNReal.ofReal_lt_top
  have hYint : Integrable Y μ := hYmem.integrable (by norm_num)
  have hYmean : (∫ ω, Y ω ∂μ) ≤ (1557 / 1000 : ℝ) * β ^ 4 :=
    real_integral_le_of_lintegral_ofReal Y hYint (Filter.Eventually.of_forall hY0) _ hF0 hYexp
  let B : Cutoff.CutoffSample 2 → ℝ := bnew M m Q
  let R : Cutoff.CutoffSample 2 → ℝ := fun ω => max (B ω - 14103 / 10000) 0
  have hR0 (ω : Cutoff.CutoffSample 2) : 0 ≤ R ω := le_max_right _ _
  have hBcap : eLpNorm B 128 μ ≤ ENNReal.ofReal (14103 / 10000 : ℝ) := hB128
  have hRcap : eLpNorm R (ENNReal.ofReal 128) μ ≤ ENNReal.ofReal (5 / 10 ^ 24 : ℝ) := by
    simpa [R, B] using hR128
  have hmain := positive_rare_split_weighted_integral_cap B R Y (14103 / 10000 : ℝ)
    ((1557 / 1000 : ℝ) * β ^ 4) ((513 / 500 : ℝ) * ((1557 / 1000 : ℝ) * β ^ 4)) (by norm_num)
    (by positivity)
    (Filter.Eventually.of_forall fun ω => by
      have := le_max_left (B ω - 14103 / 10000) 0
      simp only [R]; linarith)
    hR0 hY0 hBcap hRcap hYL hYmean
  have hBmem : MemLp B 128 μ :=
    lt_of_le_of_lt hBcap ENNReal.ofReal_lt_top
  have hconj : (128 : ℝ).HolderConjugate (128 / 127 : ℝ) := by
    rw [Real.holderConjugate_iff_eq_conjExponent (by norm_num : (1 : ℝ) < 128)]
    norm_num
  letI : ENNReal.HolderTriple 128 (ENNReal.ofReal (128 / 127 : ℝ)) 1 := by
    simpa using hconj.ennrealOfReal
  have hBYint : Integrable (fun ω => B ω * Y ω) μ := hBmem.integrable_mul hYmem
  set c : ℝ := (((CC).σ ^ 2)⁻¹ : ℝ) ^ 2 with hc
  have hPeq : P = fun ω => c * (B ω * Y ω) := rfl
  have hc0 : 0 ≤ c := by positivity
  have hFc : 0 ≤ Fc := by positivity
  refine ⟨hFc, ?_, ?_, ?_⟩
  · rw [hPeq]; exact (hBm.mul hYmeas).const_mul c
  · rw [hPeq]; exact hBYint.const_mul c
  · rw [hPeq, integral_const_mul]
    have hid : c * ((14103 / 10000 : ℝ) * ((1557 / 1000 : ℝ) * β ^ 4) +
        (5 / 10 ^ 24 : ℝ) * ((513 / 500 : ℝ) * ((1557 / 1000 : ℝ) * β ^ 4))) =
        ((CC).amp ^ 2) ^ 2 * Fc := by
      rw [hamp, hc]
      simp only [Fc]
      field_simp
    rw [← hid]
    exact mul_le_mul_of_nonneg_left hmain hc0

end Final

end

end ASDExplicitGamma.Scalar
