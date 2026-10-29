module

public import ASDExplicitGamma.Inverse.CompatibleGluing

/-! The countable parent H1 limit has the actual pointwise series as its
representative almost everywhere. Both values and weak derivatives are
identified, rather than merely constructing an unspecified H1 witness. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory
open scoped ENNReal
noncomputable section

local instance stoppedSeriesRepresentativeTwo : Fact ((1:ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

theorem compatible_series_function_ae_hasSum {U : Set (Vec 2)}
    (F : ℕ → H1Function U)
    (hfun : Summable (fun a => ‖compatibleFunctionLpTerm (F a)‖))
    (hgrad : ∀ k, Summable (fun a => compatibleGradientLpTerm (F a) k)) :
    ∀ᵐ x ∂volumeMeasureOn U, HasSum (fun a => (F a).toFun x)
      ((compatibleSeriesLimit F hfun.of_norm hgrad).toFun x) := by
  have hn : (∑' a, ‖compatibleFunctionLpTerm (F a)‖ₑ) ≠ ∞ :=
    tsum_enorm_ne_top_iff_summable_norm.mpr hfun
  filter_upwards [Lp.hasSum_coeFn_tsum hn,
    ae_all_iff.mpr (fun a => (F a).memL2.coeFn_toLp)] with x hx hterms
  have he : (fun a => compatibleFunctionLpTerm (F a) x) = fun a => (F a).toFun x :=
    funext hterms
  rw [he] at hx
  exact hx

theorem compatible_series_gradient_ae_hasSum {U : Set (Vec 2)}
    (F : ℕ → H1Function U)
    (hfun : Summable (fun a => compatibleFunctionLpTerm (F a)))
    (hgrad : ∀ k, Summable (fun a => ‖compatibleGradientLpTerm (F a) k‖)) (k : Fin 2) :
    ∀ᵐ x ∂volumeMeasureOn U, HasSum (fun a => (F a).grad x k)
      ((compatibleSeriesLimit F hfun (fun i => (hgrad i).of_norm)).grad x k) := by
  have hn : (∑' a, ‖compatibleGradientLpTerm (F a) k‖ₑ) ≠ ∞ :=
    tsum_enorm_ne_top_iff_summable_norm.mpr (hgrad k)
  filter_upwards [Lp.hasSum_coeFn_tsum hn,
    ae_all_iff.mpr (fun a => ((F a).gradMemL2 k).coeFn_toLp)] with x hx hterms
  have he : (fun a => compatibleGradientLpTerm (F a) k x) = fun a => (F a).grad x k :=
    funext hterms
  rw [he] at hx
  exact hx

end
end ASDExplicitGamma.Inverse
