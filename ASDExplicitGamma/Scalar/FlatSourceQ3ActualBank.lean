module

public import ASDExplicitGamma.Scalar.FlatSourceQ3ActualL128
public import ASDExplicitGamma.Scalar.FlatSourceFiniteWick
public import ASDExplicitGamma.Inverse.BridgeGlobalBank

/-! The actual global NEW inverse-bank split against the fixed physical q3
flat-source positive-Haar energy. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Homogenization Filter
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic
open ASDExplicitGamma.Variational
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped ENNReal

namespace ASDExplicitGamma.Scalar

set_option linter.constructorNameAsVariable false
/-- The actual global `B*` is nonnegative because every complete inverse
history in its finite observer family is nonnegative. -/
lemma mixed_bridge_bstar_nonneg
    (M : ABKModel 2) (m : ℤ) (t : ℝ) (ω : Cutoff.CutoffSample 2) :
    0 ≤ mixedBridgeBstar M m t ω := by
  have hq : 1 < (3 : ℝ) ^ (1 / 4 : ℝ) :=
    Real.one_lt_rpow (by norm_num) (by norm_num)
  have hroot (U : TriadicCube 2) :
      0 ≤ mixedBridgeRootHistoryProfile M m t ω U := by
    unfold mixedBridgeRootHistoryProfile
    exact mul_nonneg (Annealed.sigmaBar_characterization M m).1.le
      (lemmaVInverseHistory_nonneg U
        (Model.partialInsertedCoefficient M m t ω).toFun hq)
  unfold mixedBridgeBstar
  exact Book.Ch02.finsetSupReal_nonneg _ _ (fun U hU => hroot U)
set_option linter.constructorNameAsVariable true

/-- A measurable nonnegative source energy with an Lq cap and a separate mean
cap can be weighted by a bank split while charging only the rare part to
Hölder. -/
theorem positive_rare_split_weighted_integral_cap
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (B R Y : Ω → ℝ) (b F Cq : ℝ)
    (hb : 0 ≤ b) (hCq : 0 ≤ Cq)
    (hsplit : ∀ᵐ ω ∂μ, B ω ≤ b + R ω)
    (hR0 : ∀ ω, 0 ≤ R ω) (hY0 : ∀ ω, 0 ≤ Y ω)
    (hBcap : eLpNorm B 128 μ ≤ ENNReal.ofReal b)
    (hRcap : eLpNorm R (ENNReal.ofReal 128) μ ≤ ENNReal.ofReal (5 / 10^24 : ℝ))
    (hYcap : eLpNorm Y (ENNReal.ofReal (128 / 127 : ℝ)) μ ≤ ENNReal.ofReal Cq)
    (hYmean : (∫ ω, Y ω ∂μ) ≤ F) :
    (∫ ω, B ω * Y ω ∂μ) ≤ b * F + (5 / 10^24 : ℝ) * Cq := by
  have hBmem : MemLp B 128 μ := by
    rw [memLp_iff]
    exact lt_of_le_of_lt hBcap ENNReal.ofReal_lt_top
  have hRmem : MemLp R (ENNReal.ofReal 128) μ := by
    rw [memLp_iff]
    exact lt_of_le_of_lt hRcap ENNReal.ofReal_lt_top
  have hYmem : MemLp Y (ENNReal.ofReal (128 / 127 : ℝ)) μ := by
    rw [memLp_iff]
    exact lt_of_le_of_lt hYcap ENNReal.ofReal_lt_top
  have hconj : (128 : ℝ).HolderConjugate (128 / 127 : ℝ) := by
    rw [Real.holderConjugate_iff_eq_conjExponent
      (by norm_num : (1 : ℝ) < 128)]
    norm_num
  letI : ENNReal.HolderTriple 128
      (ENNReal.ofReal (128 / 127 : ℝ)) 1 := by
    simpa using hconj.ennrealOfReal
  letI : ENNReal.HolderTriple (ENNReal.ofReal 128)
      (ENNReal.ofReal (128 / 127 : ℝ)) 1 := hconj.ennrealOfReal
  have hRare := flat_source_rare_product_holder μ R Y hCq hR0 hY0
    hRmem hYmem hRcap hYcap
  have hYint : Integrable Y μ := hYmem.integrable (by norm_num)
  have hBYint : Integrable (fun ω => B ω * Y ω) μ := hBmem.integrable_mul hYmem
  have hRYint : Integrable (fun ω => R ω * Y ω) μ := hRmem.integrable_mul hYmem
  have hsumInt : Integrable (fun ω => b * Y ω + R ω * Y ω) μ :=
    (hYint.const_mul b).add hRYint
  have hpoint : ∀ᵐ ω ∂μ, B ω * Y ω ≤ b * Y ω + R ω * Y ω := by
    filter_upwards [hsplit] with ω hω
    calc
      B ω * Y ω ≤ (b + R ω) * Y ω := mul_le_mul_of_nonneg_right hω (hY0 ω)
      _ = b * Y ω + R ω * Y ω := by ring
  have hweighted := integral_mono_ae hBYint hsumInt hpoint
  have hweighted' :
      (∫ ω, B ω * Y ω ∂μ) ≤ b * (∫ ω, Y ω ∂μ) + ∫ ω, R ω * Y ω ∂μ := by
    rw [integral_add (hYint.const_mul b) hRYint] at hweighted
    simpa [integral_const_mul] using hweighted
  exact hweighted'.trans (add_le_add (mul_le_mul_of_nonneg_left hYmean hb) hRare)

/-- Convert an ENNReal positive expectation bound to the real integral used by
the weighted source estimate. -/
theorem real_integral_le_of_lintegral_ofReal
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (f : Ω → ℝ) (hf : Integrable f μ) (hnonneg : ∀ᵐ ω ∂μ, 0 ≤ f ω)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∫⁻ ω, ENNReal.ofReal (f ω) ∂μ ≤ ENNReal.ofReal C) :
    (∫ ω, f ω ∂μ) ≤ C := by
  have hreal : ENNReal.ofReal (∫ ω, f ω ∂μ) ≤ ENNReal.ofReal C := by
    rw [ofReal_integral_eq_lintegral_ofReal hf hnonneg]
    exact hbound
  exact (ENNReal.ofReal_le_ofReal_iff hC).1 hreal

end ASDExplicitGamma.Scalar
