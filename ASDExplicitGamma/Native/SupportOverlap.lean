module

public import ASDExplicitGamma.Gaussian.SpatialKernelLocalization
public import ASDExplicitGamma.Gaussian.Q3CameronMartinSeries
public import Mathlib.Algebra.Order.Chebyshev

/-! # Finite support-overlap bound for averaged white-noise gradients -/

@[expose] public section

open MeasureTheory Set Homogenization ASDExplicitGamma.Gaussian
open scoped RealInnerProductSpace

namespace ASDExplicitGamma.Native

/-- The q3 kernel support enlargement of an axis-parallel rectangle. -/
def q3ExpandedRectangle (a b c d : ℝ) (L : {l : ℝ // 0 < l}) : Set (Vec 2) :=
  closedRectangle (a - L.1 / 2) (b + L.1 / 2) (c - L.1 / 2) (d + L.1 / 2)

theorem q3ExpandedRectangle_measurable (a b c d : ℝ) (L : {l : ℝ // 0 < l}) :
    MeasurableSet (q3ExpandedRectangle a b c d L) :=
  (closedRectangle_isCompact _ _ _ _).measurableSet

/-- Every value-kernel section centered in a rectangle is supported in its
q3-enlargement. -/
theorem q3SectionFunction_zero_outside_expandedRectangle
    (β : ℝ) (L : {l : ℝ // 0 < l}) (a b c d : ℝ)
    (x : closedRectangle a b c d) {y : Vec 2}
    (hy : y ∉ q3ExpandedRectangle a b c d L) :
    q3SectionFunction β L h3Zero x.1 y = 0 := by
  have hnot : y ∉ q3SupportBox L x.1 := by
    intro hybox
    have hcoord : ∀ i : Fin 2, dist (y i) (x.1 i) ≤ L.1 / 2 :=
      (dist_pi_le_iff (div_nonneg L.2.le (by norm_num))).mp hybox
    have habs (i : Fin 2) : |y i - x.1 i| ≤ L.1 / 2 := by
      simpa [Real.dist_eq, abs_sub_comm] using hcoord i
    have hx0 := x.2.1
    have hx1 := x.2.2
    have habs0 := abs_le.mp (habs 0)
    have habs1 := abs_le.mp (habs 1)
    have hy0 : y 0 ∈ Icc (a - L.1 / 2) (b + L.1 / 2) := by
      constructor <;> nlinarith [habs0.1, habs0.2, hx0.1, hx0.2]
    have hy1 : y 1 ∈ Icc (c - L.1 / 2) (d + L.1 / 2) := by
      constructor <;> nlinarith [habs1.1, habs1.2, hx1.1, hx1.2]
    exact hy ⟨hy0, hy1⟩
  exact q3SectionFunction_zero_outside β L x.1 y hnot

/-- Restrict a white-noise input to a measurable spatial set. -/
noncomputable def whiteNoiseRestrict (A : Set (Vec 2)) (hA : MeasurableSet A)
    (u : WhiteNoise) : WhiteNoise :=
  ((Lp.memLp u).indicator hA).toLp (A.indicator u)

theorem whiteNoiseRestrict_ae (A : Set (Vec 2)) (hA : MeasurableSet A)
    (u : WhiteNoise) :
    whiteNoiseRestrict A hA u =ᵐ[volume] A.indicator u :=
  ((Lp.memLp u).indicator hA).coeFn_toLp

/-- Restricting the white noise input to a set containing a kernel section's
support does not change the corresponding q3 convolution observation. -/
theorem inner_whiteNoiseRestrict_q3Section
    (A : Set (Vec 2)) (hA : MeasurableSet A) (u : WhiteNoise)
    (β : ℝ) (L : {l : ℝ // 0 < l}) (x : Vec 2)
    (hzero : ∀ y, y ∉ A → q3SectionFunction β L h3Zero x y = 0) :
    ⟪whiteNoiseRestrict A hA u, q3Section β L h3Zero x⟫ =
      ⟪u, q3Section β L h3Zero x⟫ := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [whiteNoiseRestrict_ae A hA u,
    (q3SectionFunction_memLp β L h3Zero x).coeFn_toLp] with y hu hk
  change q3Section β L h3Zero x y = q3SectionFunction β L h3Zero x y at hk
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, hu, hk]
  by_cases hy : y ∈ A
  · rw [Set.indicator_of_mem hy]
  · rw [Set.indicator_of_notMem hy, hzero y hy]
    simp

/-- A centered physical q3 remainder factor depends only on the white noise
inside any measurable set containing the supports of its kernel sections. -/
theorem q3RemainderValueFactor_restrict_eq
    (a b c d β : ℝ) (hab : a < b) (hcd : c < d)
    (L : {l : ℝ // 0 < l}) (x₀ : closedRectangle a b c d)
    (A : Set (Vec 2)) (hA : MeasurableSet A) (u : WhiteNoise)
    (hzero : ∀ x : closedRectangle a b c d, ∀ y, y ∉ A →
      q3SectionFunction β L h3Zero x.1 y = 0) :
    q3RemainderValueFactor a b c d β L x₀ (whiteNoiseRestrict A hA u) =
      q3RemainderValueFactor a b c d β L x₀ u := by
  ext x
  simp only [q3RemainderValueFactor, ContinuousLinearMap.comp_apply,
    centeringMap_apply]
  rw [q3H3RangeValue_factor a b c d β hab hcd L (whiteNoiseRestrict A hA u) x,
    q3H3RangeValue_factor a b c d β hab hcd L u x,
    q3H3RangeValue_factor a b c d β hab hcd L (whiteNoiseRestrict A hA u) x₀,
    q3H3RangeValue_factor a b c d β hab hcd L u x₀]
  rw [inner_whiteNoiseRestrict_q3Section A hA u β L x.1 (hzero x),
    inner_whiteNoiseRestrict_q3Section A hA u β L x₀.1 (hzero x₀)]

/-- The physical centered remainder is local to the q3-enlarged observation
rectangle. -/
theorem q3RemainderValueFactor_local
    (a b c d β : ℝ) (hab : a < b) (hcd : c < d)
    (L : {l : ℝ // 0 < l}) (x₀ : closedRectangle a b c d)
    (u : WhiteNoise) :
    q3RemainderValueFactor a b c d β L x₀
        (whiteNoiseRestrict (q3ExpandedRectangle a b c d L)
          (q3ExpandedRectangle_measurable a b c d L) u) =
      q3RemainderValueFactor a b c d β L x₀ u := by
  apply q3RemainderValueFactor_restrict_eq a b c d β hab hcd L x₀
    (q3ExpandedRectangle a b c d L) (q3ExpandedRectangle_measurable a b c d L) u
  intro x y hy
  exact q3SectionFunction_zero_outside_expandedRectangle β L a b c d x hy

/-- If a continuous linear observation depends only on input in `A`, its
Riesz representative is supported in `A`. This converts operator locality
into the support hypothesis consumed by the overlap estimate. -/
theorem whiteNoiseRiesz_support_of_local
    (A : Set (Vec 2)) (hA : MeasurableSet A)
    (L : WhiteNoise →L[ℝ] ℝ)
    (hlocal : ∀ u, L u = L (whiteNoiseRestrict A hA u)) :
    ∀ᵐ x : Vec 2 ∂(volume : Measure (Vec 2)),
      x ∉ A → ((InnerProductSpace.toDual ℝ WhiteNoise).symm L) x = 0 := by
  let r : WhiteNoise := (InnerProductSpace.toDual ℝ WhiteNoise).symm L
  let v : WhiteNoise := whiteNoiseRestrict Aᶜ hA.compl r
  have hvA : whiteNoiseRestrict A hA v = 0 := by
    apply Lp.ext
    filter_upwards [whiteNoiseRestrict_ae A hA v,
      whiteNoiseRestrict_ae Aᶜ hA.compl r] with x hv hv'
    change whiteNoiseRestrict A hA v x = A.indicator v x at hv
    change v x = Aᶜ.indicator r x at hv'
    rw [hv]
    by_cases hx : x ∈ A
    · have hnot : x ∉ Aᶜ := by simpa using hx
      rw [Set.indicator_of_mem hx, hv']
      simp [hnot]
    · simp [hx]
  have hLv : L v = 0 := by
    calc
      L v = L (whiteNoiseRestrict A hA v) := hlocal v
      _ = 0 := by rw [hvA, map_zero]
  have hdual (u : WhiteNoise) : L u = ⟪r, u⟫ := by
    exact (congrArg (fun f : WhiteNoise →L[ℝ] ℝ => f u)
      ((InnerProductSpace.toDual ℝ WhiteNoise).apply_symm_apply L)).symm
  have hinner : ⟪r, v⟫ = ‖v‖ ^ 2 := by
    rw [L2.inner_def, l2_norm_sq]
    apply integral_congr_ae
    filter_upwards [whiteNoiseRestrict_ae Aᶜ hA.compl r] with x hxv
    change v x = Aᶜ.indicator r x at hxv
    by_cases hx : x ∈ A
    · have hnot : x ∉ Aᶜ := by simpa using hx
      simp [hnot, hxv]
    · have hmem : x ∈ Aᶜ := by simpa using hx
      simp [hmem, hxv, Real.norm_eq_abs, sq_abs]
  have hvzero : v = 0 := by
    have hz : ‖v‖ ^ 2 = 0 := by
      rw [← hinner, ← hdual v, hLv]
    have hnorm : ‖v‖ = 0 := by nlinarith [norm_nonneg v]
    exact norm_eq_zero.mp hnorm
  filter_upwards [whiteNoiseRestrict_ae Aᶜ hA.compl r] with x hxv hnot
  change v x = Aᶜ.indicator r x at hxv
  have hmem : x ∈ Aᶜ := by simpa using hnot
  have hxval : v x = r x := by simpa [hmem] using hxv
  rw [← hxval]
  simp [hvzero]

/-- Every continuous observation of the actual centered q3 remainder has a
white-noise Riesz gradient supported in the enlarged rectangle. -/
theorem q3RemainderObservation_riesz_support
    (a b c d β : ℝ) (hab : a < b) (hcd : c < d)
    (L : {l : ℝ // 0 < l}) (x₀ : closedRectangle a b c d)
    (O : C(closedRectangle a b c d, ℝ) →L[ℝ] ℝ) :
    ∀ᵐ y : Vec 2 ∂(volume : Measure (Vec 2)),
      y ∉ q3ExpandedRectangle a b c d L →
        ((InnerProductSpace.toDual ℝ WhiteNoise).symm
          (O.comp (q3RemainderValueFactor a b c d β L x₀))) y = 0 := by
  apply whiteNoiseRiesz_support_of_local
    (q3ExpandedRectangle a b c d L)
    (q3ExpandedRectangle_measurable a b c d L)
  intro u
  exact (congrArg O (q3RemainderValueFactor_local a b c d β hab hcd L x₀ u)).symm

/-- An average of square-integrable white-noise gradients gains the support
overlap multiplicity. `U x` lists the indices whose support contains `x`. -/
theorem whiteNoise_average_sq_le_supportOverlap
    {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (X : ι → WhiteNoise) (A : ι → Set (Vec 2)) (U : Vec 2 → Finset ι) (M : ℝ)
    (hM : 0 ≤ M) (hN : 0 < (S.card : ℝ))
    (hactive : ∀ x i, i ∈ U x ↔ x ∈ A i)
    (hzero : ∀ i ∈ S, ∀ᵐ x : Vec 2 ∂(volume : Measure (Vec 2)),
      x ∉ A i → X i x = 0)
    (hoverlap : ∀ᵐ x : Vec 2 ∂(volume : Measure (Vec 2)),
      ((S ∩ U x).card : ℝ) ≤ M) :
    ‖((S.card : ℝ)⁻¹) • ∑ i ∈ S, X i‖ ^ 2 ≤
      M * ((S.card : ℝ)⁻¹) ^ 2 * ∑ i ∈ S, ‖X i‖ ^ 2 := by
  classical
  let N : ℝ := S.card
  have hN' : 0 < N := hN
  have hzeroAE : ∀ᵐ x : Vec 2 ∂(volume : Measure (Vec 2)),
      ∀ i ∈ S, x ∉ A i → X i x = 0 := by
    filter_upwards [(Finset.eventually_all S).2 (fun i hi => hzero i hi)] with x hx i hi hnot
    exact hx i hi hnot
  have hpoint : ∀ᵐ x : Vec 2 ∂(volume : Measure (Vec 2)),
      (N⁻¹ * (∑ i ∈ S, X i x)) ^ 2 ≤
        N⁻¹ ^ 2 * (M * ∑ i ∈ S, (X i x) ^ 2) := by
    filter_upwards [hzeroAE, hoverlap] with x hx hz
    let V : Finset ι := S ∩ U x
    have hsum : (∑ i ∈ S, X i x) = ∑ i ∈ V, X i x := by
      rw [← Finset.sum_filter_add_sum_filter_not S (fun i => i ∈ U x) (fun i => X i x)]
      have hfilter : S.filter (fun i => i ∈ U x) = V := by
        ext i
        simp [V, Finset.mem_inter]
      have hzeroSum : ∑ i ∈ S.filter (fun i => ¬ i ∈ U x), X i x = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have hiS := (Finset.mem_filter.mp hi).1
        have hinot := (Finset.mem_filter.mp hi).2
        apply hx i hiS
        intro hmem
        exact hinot ((hactive x i).mpr hmem)
      rw [hfilter, hzeroSum, add_zero]
    have hcheb := sq_sum_le_card_mul_sum_sq (s := V) (f := fun i => X i x)
    have hsub : V ⊆ S := Finset.inter_subset_left
    have hsumSq : (∑ i ∈ V, (X i x) ^ 2) ≤ ∑ i ∈ S, (X i x) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => sq_nonneg (X i x))
    have hcard : (V.card : ℝ) ≤ M := hz
    have hraw : (∑ i ∈ V, X i x) ^ 2 ≤ M * ∑ i ∈ S, (X i x) ^ 2 := by
      calc
        (∑ i ∈ V, X i x) ^ 2 ≤ (V.card : ℝ) * ∑ i ∈ V, (X i x) ^ 2 := hcheb
        _ ≤ M * ∑ i ∈ S, (X i x) ^ 2 :=
          mul_le_mul hcard hsumSq (Finset.sum_nonneg fun i _ => sq_nonneg (X i x))
            hM
    rw [hsum]
    calc
      (N⁻¹ * (∑ i ∈ V, X i x)) ^ 2 = N⁻¹ ^ 2 * (∑ i ∈ V, X i x) ^ 2 := by ring
      _ ≤ N⁻¹ ^ 2 * (M * ∑ i ∈ S, (X i x) ^ 2) :=
        mul_le_mul_of_nonneg_left hraw (sq_nonneg N⁻¹)
  have hnormAE : (fun x : Vec 2 =>
      ‖(N⁻¹ • (∑ i ∈ S, X i)) x‖ ^ 2) =ᵐ[volume]
      fun x => (N⁻¹ * (∑ i ∈ S, X i x)) ^ 2 := by
    filter_upwards [Lp.coeFn_smul N⁻¹ (∑ i ∈ S, X i), Lp.coeFn_finsetSum S X]
      with x hx hs
    change (N⁻¹ • (∑ i ∈ S, X i) : WhiteNoise) x = _ at hx
    change (∑ i ∈ S, X i) x = _ at hs
    have hs' : (∑ i ∈ S, X i) x = ∑ i ∈ S, X i x := by
      simpa only [Finset.sum_apply] using hs
    have hval : (N⁻¹ • (∑ i ∈ S, X i) : WhiteNoise) x =
        N⁻¹ * (∑ i ∈ S, X i x) := by
      rw [hx]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hs']
    rw [hval]
    simp only [Real.norm_eq_abs]
    rw [mul_pow, sq_abs]
    ring
  have hleft : ‖N⁻¹ • (∑ i ∈ S, X i)‖ ^ 2 =
      ∫ x : Vec 2, (N⁻¹ * (∑ i ∈ S, X i x)) ^ 2 := by
    rw [l2_norm_sq, integral_congr_ae hnormAE]
  have hXi (i : ι) : (∫ x : Vec 2, (X i x) ^ 2) = ‖X i‖ ^ 2 := by
    calc
      (∫ x : Vec 2, (X i x) ^ 2) = ∫ x : Vec 2, ‖X i x‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards with x
        simp only [Real.norm_eq_abs, sq_abs]
      _ = ‖X i‖ ^ 2 := (l2_norm_sq volume (X i)).symm
  have hXiInt (i : ι) : Integrable (fun x : Vec 2 => (X i x) ^ 2) volume := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (Lp.memLp (X i)).integrable_norm_pow (by norm_num : 2 ≠ 0)
  have hright :
      (∫ x : Vec 2, N⁻¹ ^ 2 * (M * ∑ i ∈ S, (X i x) ^ 2)) =
        M * N⁻¹ ^ 2 * ∑ i ∈ S, ‖X i‖ ^ 2 := by
    calc
      _ = N⁻¹ ^ 2 * (M * ∫ x : Vec 2, ∑ i ∈ S, (X i x) ^ 2) := by
        rw [integral_const_mul, integral_const_mul]
      _ = N⁻¹ ^ 2 * (M * ∑ i ∈ S, ∫ x : Vec 2, (X i x) ^ 2) := by
        rw [integral_finsetSum _ (fun i hi => hXiInt i)]
      _ = M * N⁻¹ ^ 2 * ∑ i ∈ S, ‖X i‖ ^ 2 := by
        simp_rw [hXi]
        ring
  have hleftInt : Integrable (fun x : Vec 2 =>
      (N⁻¹ * (∑ i ∈ S, X i x)) ^ 2) volume := by
    have hbase := (Lp.memLp (N⁻¹ • (∑ i ∈ S, X i))).integrable_norm_pow
      (by norm_num : 2 ≠ 0)
    exact (integrable_congr hnormAE).mp hbase
  have hrightInt : Integrable (fun x : Vec 2 =>
      N⁻¹ ^ 2 * (M * ∑ i ∈ S, (X i x) ^ 2)) volume := by
    have hsum : Integrable (fun x : Vec 2 => ∑ i ∈ S, (X i x) ^ 2) volume :=
      integrable_finsetSum _ (fun i hi => hXiInt i)
    convert (hsum.const_mul (N⁻¹ ^ 2 * M)) using 1
    ext x
    ring
  have hmono := integral_mono_ae hleftInt hrightInt hpoint
  dsimp [N] at hleft hright ⊢
  rw [hleft]
  exact hmono.trans_eq hright

end ASDExplicitGamma.Native
