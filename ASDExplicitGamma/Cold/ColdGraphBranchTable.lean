module

public import ASDExplicitGamma.Cold.ColdGraphRadicandTable
public import ASDExplicitGamma.Cold.ColdGraphAnalytic

/-! # Soundness of the selected five-sixths and sandwich graph branches -/

@[expose] public section
noncomputable section
namespace ASDExplicitGamma.Cold
open ASDExplicitGamma.Numerics.Cold

/-- A nonnegative real graph norm below the two producing inputs fits the rounded square. -/
theorem cold_graph_square_table {e x : ℝ} {E X : ℚ} (he : 0 ≤ e) (hx : 0 ≤ x)
    (hE : e ≤ (E:ℝ)) (hX : x ≤ (X:ℝ)) :
    2*(e+x)^2 ≤ ((2*(coldUpAdd E X)^2:ℚ):ℝ) := by
  have hs := cold_up_add_mono hE hX
  have hp := (sq_le_sq₀ (add_nonneg he hx) ((add_nonneg he hx).trans hs)).mpr hs
  push_cast
  linarith only [hp]

/-- A selected five-sixths source candidate fits the rational producing graph branch. -/
theorem cold_five_sixths_graph_table {ell k : ℕ} (hell : ell ≤ 126) (hk : k ≤ 126)
    (hchoice : coldGraphChoiceAt ell ≠ 0) (hodd : coldGraphChoiceAt ell % 2 = 1)
    (hkchoice : k = (coldGraphChoiceAt ell-1)/2) :
    coldFiveSixthsGraphCap (coldMeanAt k:ℝ) (coldInterpolationAt k:ℝ) (ell-k) ≤
      (coldFiveSixthsGraph ell k:ℝ) := by
  have hmem : ell ∈ coldCheckedGraphLags := List.mem_range.mpr (by omega)
  have hinput := cold_graph_root_input_check ell hmem hchoice
  have heq : coldGraphSqrtInputAt ell = coldFiveSixthsRadicand ell k := by
    rw [hinput,coldGraphRadicand,ite_eq_right hchoice,ite_eq_left hodd,← hkchoice]
  have hroot := cold_graph_root_table hell hchoice ((cold_five_sixths_radicand_table ell k).trans_eq
    (congrArg (fun x : ℚ => (x:ℝ)) heq.symm))
  dsimp only [coldFiveSixthsGraphCap,coldFiveSixthsGraph]
  have he0 : 0 ≤ 2*(3:ℝ)^(-((ell-k:ℕ):ℝ))*Real.sqrt (2*(coldMeanAt k:ℝ)+(coldInterpolationAt k:ℝ)^2) :=
    mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _)) (Real.sqrt_nonneg _)
  exact cold_graph_square_table (E := coldRoundUp (2*coldDecay (ell-k)*coldVUpper k))
    (X := coldGraphRootAt ell) he0 (Real.sqrt_nonneg _)
    (cold_graph_e_table hk ell) hroot

/-- A selected sandwich source candidate fits the rational producing graph branch. -/
theorem cold_sandwich_graph_table {ell k : ℕ} (hell : ell ≤ 126) (hk : k ≤ 126)
    (hchoice : coldGraphChoiceAt ell ≠ 0) (hodd : coldGraphChoiceAt ell % 2 ≠ 1)
    (hkchoice : k = (coldGraphChoiceAt ell-2)/2) :
    coldSandwichGraphCap (coldMeanAt k:ℝ) (coldInterpolationAt k:ℝ) (ell-k) ≤
      (coldSandwichGraph ell k:ℝ) := by
  have hmem : ell ∈ coldCheckedGraphLags := List.mem_range.mpr (by omega)
  have hinput := cold_graph_root_input_check ell hmem hchoice
  have heq : coldGraphSqrtInputAt ell = coldSandwichRadicand ell k := by
    rw [hinput,coldGraphRadicand,ite_eq_right hchoice,ite_eq_right hodd,← hkchoice]
  have hroot := cold_graph_root_table hell hchoice ((cold_sandwich_radicand_table hk ell).trans_eq
    (congrArg (fun x : ℚ => (x:ℝ)) heq.symm))
  dsimp only [coldSandwichGraphCap,coldSandwichGraph]
  have he0 : 0 ≤ 2*(3:ℝ)^(-((ell-k:ℕ):ℝ))*Real.sqrt (2*(coldMeanAt k:ℝ)+(coldInterpolationAt k:ℝ)^2) :=
    mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _)) (Real.sqrt_nonneg _)
  exact cold_graph_square_table (E := coldRoundUp (2*coldDecay (ell-k)*coldVUpper k))
    (X := coldGraphRootAt ell) he0 (Real.sqrt_nonneg _)
    (cold_graph_e_table hk ell) hroot

end ASDExplicitGamma.Cold
