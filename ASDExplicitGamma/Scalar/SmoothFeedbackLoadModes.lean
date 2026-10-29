/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Scalar.FlatSourceProjectedModeTrace
public import ASDExplicitGamma.Scalar.Lambda8Q3ParentOscillation
public import ASDExplicitGamma.Scalar.Lambda8CovarianceAdapter
public import ASDExplicitGamma.Gaussian.Q3SeriesCovariance

/-! The mode-sum form of the one-load energy input: the actual q3 parent
mode potentials carry total (normalized) gradient energy at most half the shell
variance. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization Triadic
open ASDExplicitGamma.Gaussian
open Algsuperdiff.Section3
open scoped BigOperators RealInnerProductSpace

noncomputable section

theorem enumerated_summable_apply' {ι V : Type*} [Countable ι] [Zero V]
    (v : ι → V) (f : V → ℝ) (hf : f 0 = 0)
    (hs : Summable (fun n => f (gaussEnumerated v n))) : Summable (fun i => f (v i)) := by
  classical
  let := Encodable.ofCountable ι
  have he : (fun n => f (gaussEnumerated v n)) =
      Function.extend Encodable.encode (fun i => f (v i)) 0 := by
    funext n
    by_cases hn : n ∈ Set.range (Encodable.encode : ι → ℕ)
    · obtain ⟨i, rfl⟩ := hn
      rw [enumerated_encode, Function.Injective.extend_apply Encodable.encode_injective]
    · rw [gaussEnumerated, Function.extend_apply' _ _ _ hn, Function.extend_apply' _ _ _ hn]
      simp [hf]
  rw [he] at hs
  exact (summable_extend_zero Encodable.encode_injective).mp hs

/-- The projected load of the continuous restriction of one q3 basis mode is
minus the gradient of the actual parent mode potential. -/
theorem lambda8_mode_projected_load_eq
    (Q : TriadicCube 2) {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    (hUK : openCubeSet Q ⊆ openRectangle a b c d)
    (β : ℝ) (L : {l : ℝ // 0 < l}) (e : Vec 2) (n : whiteBasisIndex) :
    letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
      (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
    lambda8Q3ProjectedLoadClass (isOpenBoundedConvexDomain_openCubeSet Q) a b c d hab hcd e
        (q3H3RangeValue a b c d β L (q3H3RangeFactor a b c d β L (whiteBasis n))) =
      -(lambda8Q3GaussianModeParentPotential Q β L
        (-(matVecMul ASDExplicitGamma.Response.responsePlanarJ e)) n
          ).toH1Function.gradToHilbertVectorL2 := by
  classical
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  let v : Vec 2 := -(matVecMul ASDExplicitGamma.Response.responsePlanarJ e)
  let f : C(closedRectangle a b c d, ℝ) :=
    q3H3RangeValue a b c d β L (q3H3RangeFactor a b c d β L (whiteBasis n))
  have hspec := (lambda8Q3GaussianModeParentPotential_spec Q β L v n).1
  have hload : lambda8Q3LoadClass (isOpenBoundedConvexDomain_openCubeSet Q).1.measurableSet
      a b c d hab hcd e f =
      -(toHilbertVectorL2OfVecField (lambda8H1ComponentField_memVectorL2
        (fun i => lambda8Q3GaussianModeLoadH1 Q β L v n i))) := by
    have hLoad := lambda8Q3LoadField_memVectorL2
      (isOpenBoundedConvexDomain_openCubeSet Q).1.measurableSet a b c d hab hcd e f
    have hComp := lambda8H1ComponentField_memVectorL2
      (fun i => lambda8Q3GaussianModeLoadH1 Q β L v n i)
    have hL : lambda8Q3LoadClass (isOpenBoundedConvexDomain_openCubeSet Q).1.measurableSet
        a b c d hab hcd e f = toHilbertVectorL2OfVecField hLoad := rfl
    rw [hL]
    apply Lp.ext
    filter_upwards [coeFn_toHilbertVectorL2OfVecField (U := openCubeSet Q) hLoad,
      Lp.coeFn_neg (toHilbertVectorL2OfVecField hComp),
      coeFn_toHilbertVectorL2OfVecField (U := openCubeSet Q) hComp,
      ae_restrict_mem (measurableSet_openCubeSet Q)] with x h1 h2 h3 hx
    rw [h1, h2]
    simp only [Pi.neg_apply]
    rw [h3]
    have hpt : lambda8Q3LoadField a b c d hab hcd e f x =
        -(lambda8H1ComponentField (fun i => lambda8Q3GaussianModeLoadH1 Q β L v n i) x) := by
      have hxr := hUK hx
      have hclamp := lambda8CovarianceClamp_eq_of_mem a b c d hab hcd hxr
      have hval : f ⟨x, ⟨Set.Ioo_subset_Icc_self hxr.1, Set.Ioo_subset_Icc_self hxr.2⟩⟩ =
          q3Convolution β L h3Zero (whiteBasis n) x :=
        q3H3RangeValue_factor a b c d β hab hcd L (whiteBasis n) _
      unfold lambda8Q3LoadField
      rw [hclamp, hval]
      ext i
      simp [lambda8H1ComponentField, lambda8Q3GaussianModeLoadH1, v]
      simp only [H1Function.ofContDiffOnIsOpenBoundedConvexDomain,
        H1Function.ofContDiffOnIsSobolevRegularDomain]
      ring
    change HilbertVec.ofVec (lambda8Q3LoadField a b c d hab hcd e f x) =
      -HilbertVec.ofVec (lambda8H1ComponentField
        (fun i => lambda8Q3GaussianModeLoadH1 Q β L v n i) x)
    rw [hpt]
    simp
  rw [show lambda8Q3ProjectedLoadClass (isOpenBoundedConvexDomain_openCubeSet Q) a b c d hab hcd e f =
      lambda8DirichletProjection (isOpenBoundedConvexDomain_openCubeSet Q)
        (lambda8Q3LoadClass (isOpenBoundedConvexDomain_openCubeSet Q).1.measurableSet
          a b c d hab hcd e f) from rfl, hload]
  unfold lambda8DirichletProjection at hspec ⊢
  rw [map_neg, hspec]

/-- Mode-sum form of the one-load energy input: the squared gradient norms of
the actual parent mode potentials of the q3 shell load sum to at most half
the shell variance, times the parent volume. -/
theorem lambda8_mode_energy_sum_le
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (e : Vec 2) (he : Book.Ch02.vecNorm e = 1) (k : ℤ) :
    let Q : TriadicCube 2 := originCube 2 (k + 128)
    let u : whiteBasisIndex → H10Function (openCubeSet Q) :=
      fun n => lambda8Q3ParentModePotential M h e k n
    Summable (fun n => ‖(u n).toH1Function.gradToHilbertVectorL2‖ ^ 2) ∧
      (∑' n, ‖(u n).toH1Function.gradToHilbertVectorL2‖ ^ 2) ≤
        (volume (openCubeSet Q)).toReal *
          ((h ^ 2 * (3 : ℝ) ^ (2 * M.gamma * (k : ℝ))) / 2) := by
  classical
  intro Q u
  let U := openCubeSet Q
  let a : ℝ := -(1 / 2 : ℝ) * (3 : ℝ) ^ (k + 128)
  let b : ℝ := (1 / 2 : ℝ) * (3 : ℝ) ^ (k + 128)
  let hU : IsOpenBoundedConvexDomain U := isOpenBoundedConvexDomain_openCubeSet Q
  letI : IsFiniteMeasure (volumeMeasureOn U) := hU.isFiniteMeasure_restrict_volume
  have hscale : 0 < (3 : ℝ) ^ (k + 128) := zpow_pos (by norm_num : (0 : ℝ) < 3) _
  have hab : a < b := by
    dsimp [a, b]
    nlinarith
  have hrect : U = openRectangle a b a b := by
    ext x
    simp [U, Q, openRectangle, a, b]
  have hUK : U ⊆ openRectangle a b a b := by rw [hrect]
  let β : ℝ := q3ModelAmplitude M h k
  let L : {l : ℝ // 0 < l} := q3ModelLength k
  let T := lambda8Q3ProjectedLoadClass hU a b a b hab hab e
  have hmode (n : whiteBasisIndex) :
      T (q3H3RangeValue a b a b β L (q3H3RangeFactor a b a b β L (whiteBasis n))) =
        -(u n).toH1Function.gradToHilbertVectorL2 :=
    lambda8_mode_projected_load_eq Q hab hab hUK β L e n
  have hvolne : (volume U).toReal ≠ 0 := by
    dsimp [U, Q]
    exact (volume_openCubeSet_originCube_toReal_pos (d := 2) (k + 128)).ne'
  have hdirs := q3H3Directions_summable a b a b β L whiteBasis
  have hmain := lambda8Q3ProjectedLoad_modes_energy_le hU hvolne hUK hab hab e M h hM he k
  have hsumeq : (∑' j : ℕ, ‖T (q3H3RangeValue a b a b β L
      (q3H3Directions a b a b β L whiteBasis j))‖ ^ 2) =
      ∑' n, ‖(u n).toH1Function.gradToHilbertVectorL2‖ ^ 2 := by
    have := enumerated_tsum_apply
      (fun n => q3H3RangeFactor a b a b β L (whiteBasis n))
      (fun x => ‖T (q3H3RangeValue a b a b β L x)‖ ^ 2) (by simp)
    simp only [hmode, norm_neg] at this
    exact this
  have hsummableN : Summable (fun j : ℕ => ‖T (q3H3RangeValue a b a b β L
      (q3H3Directions a b a b β L whiteBasis j))‖ ^ 2) :=
    @summable_sq_bounded_image ℕ
      (Q3H3Range a b a b β L) (HilbertVectorL2 U) inferInstance
      (instQ3H3RangeInnerProductSpace a b a b β L).toNormedSpace
      inferInstance inferInstance
      (q3H3Directions a b a b β L whiteBasis) hdirs
      (T.comp (q3H3RangeValue a b a b β L))
  have hsummable : Summable (fun n => ‖(u n).toH1Function.gradToHilbertVectorL2‖ ^ 2) := by
    have := enumerated_summable_apply'
      (fun n => q3H3RangeFactor a b a b β L (whiteBasis n))
      (fun x => ‖T (q3H3RangeValue a b a b β L x)‖ ^ 2) (by simp) hsummableN
    simpa only [hmode, norm_neg] using this
  refine ⟨hsummable, ?_⟩
  rw [← hsumeq]
  exact hmain

end

end ASDExplicitGamma.Scalar
