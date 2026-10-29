module

public import ASDExplicitGamma.Cold.ColdInterpolationTable

/-! # Outward soundness of the two graph radicands -/

@[expose] public section
noncomputable section
namespace ASDExplicitGamma.Cold
open ASDExplicitGamma.Numerics.Cold

/-- The exact five-sixths radicand is below the producing rational expression. -/
theorem cold_five_sixths_radicand_table (ell k : ℕ) :
    (5/6:ℝ)*(coldMeanAt k:ℝ)^2+
      (2*(3:ℝ)^(-((ell-k:ℕ):ℝ)))^2*(coldInterpolationAt k:ℝ)^2 ≤
        (coldFiveSixthsRadicand ell k:ℝ) := by
  have hD2 : (coldMeanAt k:ℝ)^2 ≤ (coldUpMul (coldMeanAt k) (coldMeanAt k):ℝ) := by
    simpa only [pow_two] using cold_up_mul_ge (coldMeanAt k) (coldMeanAt k)
  have hfrac := cold_round_up_real (5/6:ℚ)
  have hfirst := cold_up_mul_mono (show (0:ℝ) ≤ 5/6 by norm_num) (sq_nonneg (coldMeanAt k:ℝ))
    (by norm_num at hfrac ⊢; exact hfrac) hD2
  have hsecond := cold_round_up_real ((2*coldDecay (ell-k)*coldInterpolationAt k)^2)
  have hsecond' : (2*(3:ℝ)^(-((ell-k:ℕ):ℝ)))^2*(coldInterpolationAt k:ℝ)^2 ≤
      (coldRoundUp ((2*coldDecay (ell-k)*coldInterpolationAt k)^2):ℝ) := by
    push_cast at hsecond
    rw [cold_table_decay] at hsecond
    convert hsecond using 1; ring
  exact cold_up_add_mono hfirst hsecond'

/-- The exact centered matrix fluctuation fits the rounded e input used by both graphs. -/
theorem cold_graph_e_table {k : ℕ} (hk : k ≤ 126) (ell : ℕ) :
    2*(3:ℝ)^(-((ell-k:ℕ):ℝ))*Real.sqrt (2*(coldMeanAt k:ℝ)+(coldInterpolationAt k:ℝ)^2) ≤
      (coldRoundUp (2*coldDecay (ell-k)*coldVUpper k):ℝ) := by
  have he := mul_le_mul_of_nonneg_left (cold_variance_radical_table hk)
    (show 0 ≤ 2*(3:ℝ)^(-((ell-k:ℕ):ℝ)) by positivity)
  have hr := cold_round_up_real (2*coldDecay (ell-k)*coldVUpper k)
  push_cast at hr
  rw [cold_table_decay] at hr
  exact he.trans hr

/-- The exact half-floor sandwich radicand is below the producing rational expression. -/
theorem cold_sandwich_radicand_table {k : ℕ} (hk : k ≤ 126) (ell : ℕ) :
    (coldMeanAt k:ℝ)^2/2+2*(2*(3:ℝ)^(-((ell-k:ℕ):ℝ))*
      Real.sqrt (2*(coldMeanAt k:ℝ)+(coldInterpolationAt k:ℝ)^2))^2 ≤
        (coldSandwichRadicand ell k:ℝ) := by
  let e := 2*(3:ℝ)^(-((ell-k:ℕ):ℝ))*Real.sqrt (2*(coldMeanAt k:ℝ)+(coldInterpolationAt k:ℝ)^2)
  let E := coldRoundUp (2*coldDecay (ell-k)*coldVUpper k)
  have he : 0 ≤ e := by dsimp only [e]; positivity
  have hE : e ≤ (E:ℝ) := cold_graph_e_table hk ell
  have he2 : e^2 ≤ (E:ℝ)^2 := (sq_le_sq₀ he (he.trans hE)).mpr hE
  have hround := cold_round_up_real (E^2)
  have hsq : e^2 ≤ (coldRoundUp (E^2):ℝ) := by
    push_cast at hround
    exact he2.trans hround
  have hout := cold_round_up_real (coldMeanAt k^2/2+2*coldRoundUp (E^2))
  push_cast at hout
  have hinner : (coldMeanAt k:ℝ)^2/2+2*e^2 ≤
      (coldMeanAt k:ℝ)^2/2+2*(coldRoundUp (E^2):ℝ) := by linarith only [hsq]
  exact hinner.trans hout

/-- The kernel's nonnegative root endpoint dominates any real radicand below its input. -/
theorem cold_graph_root_table {ell : ℕ} (hell : ell ≤ 126)
    (hchoice : coldGraphChoiceAt ell ≠ 0) {x : ℝ}
    (hx : x ≤ (coldGraphSqrtInputAt ell:ℝ)) : Real.sqrt x ≤ (coldGraphRootAt ell:ℝ) := by
  have hmem : ell ∈ coldCheckedGraphLags := List.mem_range.mpr (by omega)
  have hp : (coldGraphSqrtInputAt ell:ℝ) ≤ (coldGraphRootAt ell:ℝ)^2 := by
    exact_mod_cast (cold_graph_root_endpoints_check ell hmem hchoice).1
  apply (Real.sqrt_le_iff).mpr
  exact ⟨Rat.cast_nonneg.mpr (cold_graph_table_nonneg ell hmem).2.2.1,hx.trans hp⟩

end ASDExplicitGamma.Cold
