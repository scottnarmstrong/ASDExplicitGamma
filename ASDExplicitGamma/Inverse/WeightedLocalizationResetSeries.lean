module

public import ASDExplicitGamma.Inverse.WeightedLocalizationProfileMoment
public import ASDExplicitGamma.Inverse.ResetChronology

/-! Complete height/layer sums of the literal source reset abscissae. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

/-- Nonnegative convergent factors have the genuine product-series sum. -/
theorem localization_nonnegative_product_hasSum {ι κ : Type*} (f : ι → ℝ) (g : κ → ℝ)
    (hf0 : ∀ i, 0 ≤ f i) (hg0 : ∀ j, 0 ≤ g j) {a b : ℝ} (hf : HasSum f a) (hg : HasSum g b) :
    HasSum (fun p : ι × κ => f p.1 * g p.2) (a * b) := by
  have hi (i : ι) := hg.mul_left (f i)
  have hs : Summable (fun p : ι × κ => f p.1 * g p.2) :=
    (summable_prod_of_nonneg (by intro p; exact mul_nonneg (hf0 p.1) (hg0 p.2))).mpr
      ⟨fun i => (hi i).summable, by
        simp_rw [(hi _).tsum_eq]
        exact (hf.mul_right b).summable⟩
  exact hf.mul hg hs

/-- The abscissa x_{k,h} = f_k + h + (H0 - 38) at buffer forty, indexed from k=1 and h=H0. -/
def localizationResetAbscissa (C h k : ℕ) : ℕ := C + h + localizationProfileDepth (k + 1)

/-- The abscissa agrees with the literal protected reset depth, not a new offset. -/
theorem localization_reset_abscissa_source (H0 h k : ℕ) (hH : 38 ≤ H0) :
    (localizationResetAbscissa (H0 - 38) h k : ℤ) = resetDepth (H0 + h) (k + 1) - 41 := by
  unfold localizationResetAbscissa localizationProfileDepth resetDepth
  push_cast
  omega

/-- Exact complete unweighted reset-profile series. -/
theorem localization_reset_series_hasSum (z : ℝ) (hz : 0 ≤ z) (hz1 : z < 1) (C : ℕ) :
    HasSum (fun p : ℕ × ℕ => z ^ localizationResetAbscissa C p.1 p.2)
      (z ^ C * localizationProfileT 1 z / (1 - z)) := by
  have hs : (1 : ℝ) ^ 3 * z ^ 4 < 1 := by
    simpa only [one_pow, one_mul] using pow_lt_one₀ hz hz1 (by decide : (4 : ℕ) ≠ 0)
  have hg := hasSum_geometric_of_lt_one hz hz1
  have hk := localization_profile_hasSum 1 z (by norm_num) hz hs
  simp only [one_pow, one_mul] at hk
  have hh := (localization_nonnegative_product_hasSum _ _ (fun h => pow_nonneg hz h)
    (fun k => pow_nonneg hz _) hg hk).mul_left (z ^ C)
  convert hh using 1
  · funext p
    simp only [localizationResetAbscissa, pow_add]
    ring
  · ring

/-- Exact complete first reset moment, required by the x-weighted retained PE sum. -/
theorem localization_reset_first_series_hasSum (z : ℝ) (hz : 0 ≤ z) (hz1 : z < 1) (C : ℕ) :
    HasSum (fun p : ℕ × ℕ => (localizationResetAbscissa C p.1 p.2 : ℝ) *
      z ^ localizationResetAbscissa C p.1 p.2)
      (z ^ C * ((C : ℝ) * localizationProfileT 1 z / (1 - z) +
        z * localizationProfileT 1 z / (1 - z) ^ 2 + localizationProfileTf 1 z / (1 - z))) := by
  have hs : (1 : ℝ) ^ 3 * z ^ 4 < 1 := by
    simpa only [one_pow, one_mul] using pow_lt_one₀ hz hz1 (by decide : (4 : ℕ) ≠ 0)
  have hg := hasSum_geometric_of_lt_one hz hz1
  have hm := hasSum_coe_mul_geometric_of_norm_lt_one (r := z) (by rwa [Real.norm_of_nonneg hz])
  have hk := localization_profile_hasSum 1 z (by norm_num) hz hs
  have hkm := localization_profile_moment_hasSum 1 z (by norm_num) hz hs
  simp only [one_pow, one_mul, mul_one] at hk hkm
  have ha := localization_nonnegative_product_hasSum _ _
    (fun h => mul_nonneg (Nat.cast_nonneg h) (pow_nonneg hz h)) (fun k => pow_nonneg hz _) hm hk
  have hb := localization_nonnegative_product_hasSum _ _ (fun h => pow_nonneg hz h)
    (fun k => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hz _)) hg hkm
  have hc := localization_nonnegative_product_hasSum _ _ (fun h => pow_nonneg hz h)
    (fun k => pow_nonneg hz _) hg hk
  have hh := (((hc.mul_left (C : ℝ)).add ha).add hb).mul_left (z ^ C)
  convert hh using 1
  · funext p
    simp only [localizationResetAbscissa, pow_add, Nat.cast_add]
    ring
  · ring

end ASDExplicitGamma.Inverse
