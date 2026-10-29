module

public import ASDExplicitGamma.Gaussian.Q3H3Range
public import ASDExplicitGamma.Gaussian.C1JetLimit
public import ASDExplicitGamma.Gaussian.H3Centering
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # The uniform C¹ representative is the ordinary weak H³ function -/

@[expose] public section

open MeasureTheory Homogenization Set Filter
open scoped Topology

namespace ASDExplicitGamma.Gaussian

/-- The base L² class and the actual C¹ representative agree almost everywhere on the source
open rectangle. Thus the two completed images represent the same field. -/
theorem q3H3RangeValue_ae (a b c d β : ℝ) (hab : a < b) (hcd : c < d)
    (L : {l : ℝ // 0 < l}) (v : Q3H3Range a b c d β L) :
    h3Value (openRectangle a b c d) v.1 =ᵐ[volume.restrict (openRectangle a b c d)]
      c1JetValue (q3H3RangeC1 a b c d β L v) := by
  let U := openRectangle a b c d
  let P : Q3H3Range a b c d β L →L[ℝ] Lp ℝ 2 (volume.restrict U) :=
    (h3Value U).comp (hilbertRange (q3SobolevOperator U β L)).subtypeL
  have hd := hilbertRangeFactor_denseRange (q3SobolevOperator U β L)
  obtain ⟨z, hz, hzt⟩ := mem_closure_iff_seq_limit.mp (hd v)
  choose u hu using hz
  have hut : (fun n => q3H3RangeFactor a b c d β L (u n)) = z := funext hu
  have ht : Tendsto (fun n => q3H3RangeFactor a b c d β L (u n)) atTop (𝓝 v) := by rwa [hut]
  have hP := P.continuous.tendsto v |>.comp ht
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hP).exists_seq_tendsto_ae
  have he : ∀ᵐ x ∂volume.restrict U, ∀ n : ℕ,
      P (q3H3RangeFactor a b c d β L (u (ns n))) x =
        q3Convolution β L h3Zero (u (ns n)) x := by
    apply ae_all_iff.mpr
    intro n
    exact q3Coordinate_ae U β L h3Zero (u (ns n))
  filter_upwards [hae, he, ae_restrict_mem (openRectangle_isOpen a b c d).measurableSet]
    with x hx he hxU
  have hxK : x ∈ closedRectangle a b c d :=
    ⟨Ioo_subset_Icc_self hxU.1, Ioo_subset_Icc_self hxU.2⟩
  let E := q3H3RangeEvaluation a b c d β L ⟨x, hxK⟩
  have hE := E.continuous.tendsto v |>.comp (ht.comp hns.tendsto_atTop)
  have hEeq (n : ℕ) : E (q3H3RangeFactor a b c d β L (u (ns n))) =
      q3Convolution β L h3Zero (u (ns n)) x := by
    have hh := congrArg (fun j : C1Jet (closedRectangle a b c d) => j 0 ⟨x, hxK⟩)
      (q3H3RangeC1_factor a b c d β hab hcd L (u (ns n)))
    exact hh
  have hlim : Tendsto (fun n => q3Convolution β L h3Zero (u (ns n)) x)
      atTop (𝓝 (c1JetValue (q3H3RangeC1 a b c d β L v) x)) := by
    have hv : E v = c1JetValue (q3H3RangeC1 a b c d β L v) x := by
      simp only [c1JetValue, dite_eq_left hxK]
      rfl
    rw [hv] at hE
    exact hE.congr hEeq
  have heq : (fun n => P (q3H3RangeFactor a b c d β L (u (ns n))) x) =
      fun n => q3Convolution β L h3Zero (u (ns n)) x := funext he
  dsimp only [Function.comp_apply] at hx
  rw [heq] at hx
  exact tendsto_nhds_unique hx hlim

/-- The centered ordinary-H³ image and the centered continuous first jet are the same
remainder field, rather than two unrelated bounded images. -/
theorem q3H3RemainderMap_value_ae (a b c d β : ℝ) (hab : a < b) (hcd : c < d)
    (L : {l : ℝ // 0 < l}) (x₀ : closedRectangle a b c d) (v : Q3H3Range a b c d β L) :
    h3Value (openRectangle a b c d) (q3H3RemainderMap a b c d β L x₀ v)
      =ᵐ[volume.restrict (openRectangle a b c d)]
        c1JetValue (q3C1RemainderMap a b c d β L x₀ v) := by
  let U := openRectangle a b c d
  let c₀ := q3H3RangeEvaluation a b c d β L x₀ v
  have he : h3Value U (q3H3RemainderMap a b c d β L x₀ v) =
      h3Value U v.1 - h3Value U (h3Constant U c₀) := rfl
  rw [he]
  filter_upwards [Lp.coeFn_sub (h3Value U v.1) (h3Value U (h3Constant U c₀)),
    q3H3RangeValue_ae a b c d β hab hcd L v,
    h3ConstantJet_ae U c₀ h3Zero,
    ae_restrict_mem (openRectangle_isOpen a b c d).measurableSet] with x hs hv hc hxU
  have hxK : x ∈ closedRectangle a b c d :=
    ⟨Ioo_subset_Icc_self hxU.1, Ioo_subset_Icc_self hxU.2⟩
  change h3Value U (h3Constant U c₀) x = (if h3Zero = h3Zero then c₀ else 0) at hc
  simp only [↓reduceIte] at hc
  rw [hs]
  simp only [Pi.sub_apply]
  change h3Value U v.1 x = c1JetValue (q3H3RangeC1 a b c d β L v) x at hv
  rw [hv, hc]
  simp only [c1JetValue, dite_eq_left hxK]
  change _ - c₀ = c1CenteringMap x₀ (q3H3RangeC1 a b c d β L v) 0 ⟨x, hxK⟩
  rw [c1CenteringMap_value]
  rfl

end ASDExplicitGamma.Gaussian
