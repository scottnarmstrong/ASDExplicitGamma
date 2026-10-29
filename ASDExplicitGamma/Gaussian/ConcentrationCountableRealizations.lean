/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Gaussian.ConcentrationMaxima
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue

/-!
# Gaussian concentration for countable finite-dimensional realizations

Finite prefixes of a jointly Gaussian sequence can have separate finite-dimensional Gaussian
realizations. Their sharp finite-maximum tails pass to the countable supremum by dominated
convergence for the means and continuity of measure from below for the events.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal RealInnerProductSpace

namespace ASDExplicitGamma.Gaussian

/-- The pointwise supremum of a sequence of real random variables. -/
noncomputable def gaussianRealizationSup {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (ω : Ω) : ℝ := ⨆ k, X k ω

private noncomputable def gaussianRealizationPrefixMaximum {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  (Finset.univ : Finset (Fin (N + 1))).sup'
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩ fun i => X i.val ω

/-- The vector of the first `N + 1` random variables in a sequence. -/
def gaussianRealizationPrefixVector {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) : Fin (N + 1) → ℝ :=
  fun i => X i.val ω

/-- A finite vector of Gaussian linear forms with coefficient rows `a`. -/
def gaussianRealizationLinearVector {m : ℕ}
    (a : Fin m → Fin m → ℝ) (z : Fin m → ℝ) : Fin m → ℝ :=
  fun i => gaussianFiniteLinearForm (a i) z

private def gaussianRealizationVectorMaximum {m : ℕ} (hm : 0 < m)
    (y : Fin m → ℝ) : ℝ :=
  (Finset.univ : Finset (Fin m)).sup' ⟨⟨0, hm⟩, Finset.mem_univ _⟩ fun i => y i

private theorem continuous_gaussianRealizationVectorMaximum {m : ℕ} (hm : 0 < m) :
    Continuous (gaussianRealizationVectorMaximum hm) := by
  let Hne : (Finset.univ : Finset (Fin m)).Nonempty :=
    ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  change Continuous (fun y : Fin m → ℝ =>
    (Finset.univ : Finset (Fin m)).sup' Hne fun i => y i)
  apply continuous_iff_continuousAt.mpr
  intro y
  exact ContinuousAt.finset_sup'_apply (s := Finset.univ) Hne
    (f := fun (i : Fin m) (z : Fin m → ℝ) => z i)
    (fun i hi => (continuous_apply i).continuousAt)

private theorem continuous_gaussianRealizationLinearForm {n : ℕ}
    (a : Fin n → ℝ) : Continuous (gaussianFiniteLinearForm a) := by
  change Continuous (fun x : Fin n → ℝ => ∑ j, a j * x j)
  fun_prop

private theorem measurable_gaussianRealizationPrefixVector {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (X : ℕ → Ω → ℝ)
    (hX : ∀ k, AEMeasurable (X k) μ) (N : ℕ) :
    AEMeasurable (gaussianRealizationPrefixVector X N) μ := by
  apply aemeasurable_pi_iff.mpr
  intro i
  exact hX i.val

private theorem measurable_gaussianRealizationLinearVector {m : ℕ}
    (a : Fin m → Fin m → ℝ) :
    Measurable (gaussianRealizationLinearVector a) := by
  apply measurable_pi_iff.mpr
  intro i
  exact (continuous_gaussianRealizationLinearForm (a i)).measurable

private theorem gaussianRealizationLinearForm_abs_le {n : ℕ}
    (a : Fin n → ℝ) {L : ℝ}
    (hcoeff : ‖WithLp.toLp 2 a‖ ≤ L) (x : Fin n → ℝ) :
    |gaussianFiniteLinearForm a x| ≤ (n : ℝ) * L * ‖x‖ := by
  have h := gaussianFiniteLinearForm_abs_le
    (a := fun _ : Fin 1 => a)
    (hcoeff := fun _ => hcoeff) ⟨0, by omega⟩ x
  simpa [gaussianFiniteLinearForm] using h

private theorem gaussianRealizationPrefix_le_sup {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω)
    (hBdd : BddAbove (Set.range fun k => X k ω)) :
    gaussianRealizationPrefixMaximum X N ω ≤ gaussianRealizationSup X ω := by
  classical
  unfold gaussianRealizationPrefixMaximum gaussianRealizationSup
  change (Finset.univ : Finset (Fin (N + 1))).sup' (by simp)
      (fun i => X i.val ω) ≤ sSup (Set.range fun k => X k ω)
  apply Finset.sup'_le
  intro i hi
  exact le_csSup hBdd (Set.mem_range_self i.val)

private theorem tendsto_gaussianRealizationPrefixMaximum {Ω : Type*}
    [MeasurableSpace Ω] (X : ℕ → Ω → ℝ) (ω : Ω)
    (hBdd : BddAbove (Set.range fun k => X k ω)) :
    Tendsto (fun N => gaussianRealizationPrefixMaximum X N ω) atTop
      (𝓝 (gaussianRealizationSup X ω)) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    change b < sSup (Set.range fun k => X k ω) at hb
    obtain ⟨y, ⟨k, rfl⟩, hky⟩ :=
      (lt_csSup_iff hBdd (Set.range_nonempty _)).mp hb
    filter_upwards [eventually_ge_atTop k] with N hN
    have hterm : X k ω ≤ gaussianRealizationPrefixMaximum X N ω := by
      unfold gaussianRealizationPrefixMaximum
      let i : Fin (N + 1) := ⟨k, by omega⟩
      have hi := Finset.le_sup' (f := fun j : Fin (N + 1) => X j.val ω)
        (Finset.mem_univ i)
      simpa [i] using hi
    exact lt_of_lt_of_le hky hterm
  · intro b hb
    filter_upwards with N
    exact lt_of_le_of_lt (gaussianRealizationPrefix_le_sup X N ω hBdd) hb

private theorem integrable_gaussianFiniteLinearForm_countable {n : ℕ}
    (a : Fin n → ℝ) : Integrable (gaussianFiniteLinearForm a) (standardGaussianPi n) := by
  let L : ℝ := ‖WithLp.toLp 2 a‖
  let C : ℝ := (n : ℝ) * L
  have hC : 0 ≤ C := by dsimp [C, L]; positivity
  apply integrable_of_pi_polynomial_bound
    (continuous_gaussianRealizationLinearForm a).measurable hC (d := 1)
  intro x
  have hform : |gaussianFiniteLinearForm a x| ≤ C * ‖x‖ := by
    have h := gaussianRealizationLinearForm_abs_le a (L := L) le_rfl x
    simpa [C, L] using h
  calc
    |gaussianFiniteLinearForm a x| ≤ C * ‖x‖ := hform
    _ ≤ C * (1 + ‖x‖) :=
      mul_le_mul_of_nonneg_left (by linarith [norm_nonneg x]) hC
    _ = C * (1 + ‖x‖) ^ 1 := by rw [pow_one]

private theorem integrable_gaussianRealizationCoordinate {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX : ∀ k, AEMeasurable (X k) μ)
    (N : ℕ) (a : Fin (N + 1) → Fin (N + 1) → ℝ)
    (hmap : μ.map (gaussianRealizationPrefixVector X N) =
      (standardGaussianPi (N + 1)).map (gaussianRealizationLinearVector a))
    (i : Fin (N + 1)) : Integrable (X i.val) μ := by
  let Z := gaussianRealizationPrefixVector X N
  let V := gaussianRealizationLinearVector a
  let q : (Fin (N + 1) → ℝ) → ℝ := fun y => y i
  have hV : Measurable V := measurable_gaussianRealizationLinearVector a
  have hq : Measurable q := by
    dsimp [q]
    exact measurable_pi_apply i
  have hbase : Integrable (fun z => gaussianFiniteLinearForm (a i) z)
      (standardGaussianPi (N + 1)) := integrable_gaussianFiniteLinearForm_countable _
  have hqV : (fun z => q (V z)) = gaussianFiniteLinearForm (a i) := by
    funext z
    rfl
  have hqmap : Integrable q
      ((standardGaussianPi (N + 1)).map V) := by
    apply (integrable_map_measure hq.aestronglyMeasurable hV.aemeasurable).mpr
    change Integrable (fun z => q (V z)) (standardGaussianPi (N + 1))
    rw [hqV]
    exact hbase
  have hqZ : Integrable q (μ.map Z) := by rw [hmap]; exact hqmap
  have hZ : AEMeasurable Z μ := measurable_gaussianRealizationPrefixVector μ X hX N
  have hcomp := (integrable_map_measure hq.aestronglyMeasurable hZ).mp hqZ
  change Integrable (fun ω => q (Z ω)) μ at hcomp
  simpa [q, Z, gaussianRealizationPrefixVector] using hcomp

private theorem gaussianRealization_variance_eq_coefficient_norm {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX : ∀ k, AEMeasurable (X k) μ)
    (N : ℕ) (a : Fin (N + 1) → Fin (N + 1) → ℝ)
    (hmap : μ.map (gaussianRealizationPrefixVector X N) =
      (standardGaussianPi (N + 1)).map (gaussianRealizationLinearVector a))
    (i : Fin (N + 1)) :
    Var[X i.val; μ] = ‖WithLp.toLp 2 (a i)‖ ^ 2 := by
  let Z := gaussianRealizationPrefixVector X N
  let V := gaussianRealizationLinearVector a
  let q : (Fin (N + 1) → ℝ) → ℝ := fun y => y i
  have hZ : AEMeasurable Z μ := measurable_gaussianRealizationPrefixVector μ X hX N
  have hV : Measurable V := measurable_gaussianRealizationLinearVector a
  have hq : Measurable q := by
    dsimp [q]
    exact measurable_pi_apply i
  have hqZ : (q ∘ Z) = X i.val := by
    funext ω
    rfl
  have hqV : (q ∘ V) = gaussianFiniteLinearForm (a i) := by
    funext z
    rfl
  calc
    _ = Var[q ∘ Z; μ] := by rw [hqZ]
    _ = Var[q; μ.map Z] := (variance_map hq.aemeasurable hZ).symm
    _ = Var[q; (standardGaussianPi (N + 1)).map V] := by rw [hmap]
    _ = Var[q ∘ V; standardGaussianPi (N + 1)] := variance_map hq.aemeasurable hV.aemeasurable
    _ = Var[gaussianFiniteLinearForm (a i); standardGaussianPi (N + 1)] := by rw [← hqV]
    _ = ‖WithLp.toLp 2 (a i)‖ ^ 2 :=
      (integral_variance_gaussianFiniteLinearForm (a i)).2

private theorem gaussianRealization_coeff_bound_of_variance {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX : ∀ k, AEMeasurable (X k) μ)
    (N : ℕ) (a : Fin (N + 1) → Fin (N + 1) → ℝ)
    (hmap : μ.map (gaussianRealizationPrefixVector X N) =
      (standardGaussianPi (N + 1)).map (gaussianRealizationLinearVector a))
    {L : ℝ} (hL : 0 ≤ L) (hvar : ∀ k, Var[X k; μ] ≤ L ^ 2) :
    ∀ i, ‖WithLp.toLp 2 (a i)‖ ≤ L := by
  intro i
  have hsq : ‖WithLp.toLp 2 (a i)‖ ^ 2 ≤ L ^ 2 := by
    rw [← gaussianRealization_variance_eq_coefficient_norm μ X hX N a hmap i]
    exact hvar i.val
  nlinarith [norm_nonneg (WithLp.toLp 2 (a i))]

private theorem gaussianRealizationPrefix_tail {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hX : ∀ k, AEMeasurable (X k) μ)
    (N : ℕ) (a : Fin (N + 1) → Fin (N + 1) → ℝ)
    {L s : ℝ} (hL : 0 < L) (hs : 0 ≤ s)
    (hcoeff : ∀ i, ‖WithLp.toLp 2 (a i)‖ ≤ L)
    (hmap : μ.map (gaussianRealizationPrefixVector X N) =
      (standardGaussianPi (N + 1)).map (gaussianRealizationLinearVector a)) :
    Integrable (gaussianRealizationPrefixMaximum X N) μ ∧
      μ.real {ω | s ≤ gaussianRealizationPrefixMaximum X N ω -
        ∫ y, gaussianRealizationPrefixMaximum X N y ∂μ} ≤
        Real.exp (-s ^ 2 / (2 * L ^ 2)) := by
  let Z := gaussianRealizationPrefixVector X N
  let V := gaussianRealizationLinearVector a
  let m := N + 1
  let g : (Fin m → ℝ) → ℝ := gaussianRealizationVectorMaximum (Nat.succ_pos N)
  have hg : Continuous g := continuous_gaussianRealizationVectorMaximum (Nat.succ_pos N)
  have hZ : AEMeasurable Z μ := measurable_gaussianRealizationPrefixVector μ X hX N
  have hV : Measurable V := measurable_gaussianRealizationLinearVector a
  have hfinite := integral_exp_centered_le_of_gaussianFiniteMaximum
    (Nat.succ_pos N) a (L := L) (lam := 0) hcoeff
  have hbaseInt : Integrable (fun z => g (V z)) (standardGaussianPi m) := by
    apply hfinite.1.congr
    exact ae_of_all _ fun z => by
      change gaussianRealizationVectorMaximum (Nat.succ_pos N)
        (gaussianRealizationLinearVector a z) = gaussianFiniteMaximum (Nat.succ_pos N) a z
      rfl
  have hgMap : Integrable g ((standardGaussianPi m).map V) := by
    apply (integrable_map_measure hg.aestronglyMeasurable hV.aemeasurable).mpr
    exact hbaseInt
  have hgZMap : Integrable g (μ.map Z) := by rw [hmap]; exact hgMap
  have hprefixEq : (fun ω => g (Z ω)) = gaussianRealizationPrefixMaximum X N := by
    funext ω
    change gaussianRealizationVectorMaximum (Nat.succ_pos N)
      (gaussianRealizationPrefixVector X N ω) = gaussianRealizationPrefixMaximum X N ω
    rfl
  have hprefixInt : Integrable (gaussianRealizationPrefixMaximum X N) μ := by
    rw [← hprefixEq]
    exact (integrable_map_measure hg.aestronglyMeasurable hZ).mp hgZMap
  have hmeanEq : (∫ ω, gaussianRealizationPrefixMaximum X N ω ∂μ) =
      ∫ z, gaussianFiniteMaximum (Nat.succ_pos N) a z ∂standardGaussianPi m := by
    calc
      _ = ∫ y, g y ∂μ.map Z := by
        rw [← hprefixEq]
        exact (integral_map hZ hgZMap.aestronglyMeasurable).symm
      _ = ∫ y, g y ∂(standardGaussianPi m).map V := by rw [hmap]
      _ = ∫ z, g (V z) ∂standardGaussianPi m :=
        integral_map hV.aemeasurable hgMap.aestronglyMeasurable
      _ = _ := by
        apply integral_congr_ae
        exact ae_of_all _ fun z => by
          change gaussianRealizationVectorMaximum (Nat.succ_pos N)
            (gaussianRealizationLinearVector a z) = gaussianFiniteMaximum (Nat.succ_pos N) a z
          rfl
  have htail := measure_centered_tail_le_of_gaussianFiniteMaximum
    (Nat.succ_pos N) a hL hs hcoeff
  let mG : ℝ := ∫ z, gaussianFiniteMaximum (Nat.succ_pos N) a z ∂standardGaussianPi m
  let A : Set (Fin m → ℝ) := {y | s ≤ g y - mG}
  have hA : MeasurableSet A := by
    exact measurableSet_le measurable_const (hg.sub continuous_const).measurable
  have hpreZ : Z ⁻¹' A = {ω | s ≤ gaussianRealizationPrefixMaximum X N ω -
      ∫ y, gaussianRealizationPrefixMaximum X N y ∂μ} := by
    ext ω
    dsimp [A, g]
    rw [hmeanEq]
    rfl
  have hmeasureEq : μ.real {ω | s ≤ gaussianRealizationPrefixMaximum X N ω -
      ∫ y, gaussianRealizationPrefixMaximum X N y ∂μ} =
      (standardGaussianPi m).real (V ⁻¹' A) := by
    calc
      _ = (μ.map Z).real A := by rw [← hpreZ]; exact (map_measureReal_apply_of_aemeasurable hZ hA).symm
      _ = ((standardGaussianPi m).map V).real A := by rw [hmap]
      _ = (standardGaussianPi m).real (V ⁻¹' A) := map_measureReal_apply hV hA
  have hpreV' : V ⁻¹' A = {z | s ≤ gaussianFiniteMaximum (Nat.succ_pos N) a z - mG} := by
    ext z
    change s ≤ gaussianRealizationVectorMaximum (Nat.succ_pos N)
        (gaussianRealizationLinearVector a z) - mG ↔
      s ≤ gaussianFiniteMaximum (Nat.succ_pos N) a z - mG
    rw [show gaussianRealizationVectorMaximum (Nat.succ_pos N)
      (gaussianRealizationLinearVector a z) = gaussianFiniteMaximum (Nat.succ_pos N) a z by rfl]
  rw [hmeasureEq, hpreV']
  have htail' : (standardGaussianPi m).real
      {z | s ≤ gaussianFiniteMaximum (Nat.succ_pos N) a z - mG} ≤
        Real.exp (-s ^ 2 / (2 * L ^ 2)) := by
    simpa [mG] using htail.1
  exact ⟨hprefixInt, htail'⟩

/-- Sharp concentration below a threshold for the supremum of a countable centered Gaussian
sequence. Each finite prefix is given by a finite-dimensional standard Gaussian realization with
coefficient norms at most `L`; hence every variable has variance at most `L^2`. -/
private theorem measure_centered_tail_le_of_jointlyGaussianRealizations_below
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) {L s t : ℝ} (hL : 0 < L) (hs : 0 ≤ s) (hst : s < t)
    (hX : ∀ k, AEMeasurable (X k) μ)
    (hSupInt : Integrable (gaussianRealizationSup X) μ)
    (hSupFinite : ∀ᵐ ω ∂μ, BddAbove (Set.range fun k => X k ω))
    (hvar : ∀ k, Var[X k; μ] ≤ L ^ 2)
    (hrealize : ∀ N, ∃ a : Fin (N + 1) → Fin (N + 1) → ℝ,
      μ.map (gaussianRealizationPrefixVector X N) =
        (standardGaussianPi (N + 1)).map (gaussianRealizationLinearVector a)) :
    μ.real {ω | t ≤ gaussianRealizationSup X ω -
      ∫ y, gaussianRealizationSup X y ∂μ} ≤ Real.exp (-s ^ 2 / (2 * L ^ 2)) := by
  let S := gaussianRealizationSup X
  let M := gaussianRealizationPrefixMaximum X
  let m := ∫ y, S y ∂μ
  let mN := fun N => ∫ y, M N y ∂μ
  let E := fun N => {ω | s ≤ M N ω - m}
  have hXiInt : ∀ k, Integrable (X k) μ := by
    intro k
    obtain ⟨a, hmap⟩ := hrealize k
    exact integrable_gaussianRealizationCoordinate μ X hX k a hmap ⟨k, by omega⟩
  have hMInt (N : ℕ) : Integrable (M N) μ := by
    obtain ⟨a, hmap⟩ := hrealize N
    have hcoeff := gaussianRealization_coeff_bound_of_variance μ X hX N a hmap hL.le hvar
    exact (gaussianRealizationPrefix_tail μ X hX N a hL hs hcoeff hmap).1
  have hdom : Integrable (fun ω => |S ω| + |X 0 ω|) μ := by
    have h := hSupInt.norm.add (hXiInt 0).norm
    have h' : Integrable (fun ω => ‖S ω‖ + ‖X 0 ω‖) μ := by
      change Integrable
        ((fun ω => ‖gaussianRealizationSup X ω‖) + fun ω => ‖X 0 ω‖) μ
      exact h
    exact h'.congr (ae_of_all _ fun ω => by simp [Real.norm_eq_abs])
  have hbound (N : ℕ) : ∀ᵐ ω ∂μ, |M N ω| ≤ |S ω| + |X 0 ω| := by
    filter_upwards [hSupFinite] with ω hω
    have hlow : X 0 ω ≤ M N ω := by
      unfold M gaussianRealizationPrefixMaximum
      exact Finset.le_sup' (f := fun i : Fin (N + 1) => X i.val ω)
        (Finset.mem_univ ⟨0, by omega⟩)
    have hhigh : M N ω ≤ S ω := gaussianRealizationPrefix_le_sup X N ω hω
    apply abs_le.mpr
    constructor <;> dsimp [S]
    · linarith [neg_abs_le (X 0 ω), abs_nonneg (S ω)]
    · linarith [le_abs_self (S ω), abs_nonneg (X 0 ω)]
  have hmeans : Tendsto mN atTop (𝓝 m) := by
    have hpoint : ∀ᵐ ω ∂μ, Tendsto (fun N => M N ω) atTop (𝓝 (S ω)) := by
      filter_upwards [hSupFinite] with ω hω
      exact tendsto_gaussianRealizationPrefixMaximum X ω hω
    apply tendsto_integral_filter_of_dominated_convergence
      (F := M) (f := S) (bound := fun ω => |S ω| + |X 0 ω|)
    · exact Eventually.of_forall fun N => (hMInt N).aestronglyMeasurable
    · filter_upwards with N
      filter_upwards [hbound N] with ω hω
      simpa [Real.norm_eq_abs] using hω
    · exact hdom
    · exact hpoint
  have hMmono : Monotone M := by
    intro N K hNK ω
    induction hNK with
    | refl => exact le_rfl
    | @step K hNK ih =>
        apply le_trans ih
        unfold M gaussianRealizationPrefixMaximum
        apply Finset.sup'_le
        intro i hi
        let j : Fin (K + 2) := ⟨i.val, by omega⟩
        exact Finset.le_sup' (f := fun q : Fin (K + 2) => X q.val ω)
          (Finset.mem_univ j)
  have hmMono : Monotone mN := by
    intro N K hNK
    apply integral_mono_ae (hMInt N) (hMInt K)
    exact ae_of_all _ (fun ω => hMmono hNK ω)
  have hmint (N : ℕ) : mN N ≤ m := by
    have hev : ∀ᶠ K in atTop, mN N ≤ mN K := by
      filter_upwards [eventually_ge_atTop N] with K hNK
      exact hmMono hNK
    exact ge_of_tendsto hmeans hev
  have hEmono : Monotone E := by
    intro N K hNK ω hω
    dsimp [E] at hω ⊢
    exact hω.trans (sub_le_sub_right (hMmono hNK ω) m)
  have hfinite (N : ℕ) : μ.real (E N) ≤ Real.exp (-s ^ 2 / (2 * L ^ 2)) := by
    obtain ⟨a, hmap⟩ := hrealize N
    have hcoeff := gaussianRealization_coeff_bound_of_variance μ X hX N a hmap hL.le hvar
    have hprefix := (gaussianRealizationPrefix_tail μ X hX N a hL hs hcoeff hmap).2
    have hsubset : E N ⊆ {ω | s ≤ M N ω - mN N} := by
      intro ω hω
      dsimp [E, mN] at hω ⊢
      have hshift : M N ω - m ≤ M N ω - ∫ y, M N y ∂μ := by
        dsimp [m]
        linarith [hmint N]
      exact le_trans hω hshift
    exact (measureReal_mono hsubset).trans hprefix
  have hUnion : μ.real (⋃ N, E N) ≤ Real.exp (-s ^ 2 / (2 * L ^ 2)) := by
    let B := Real.exp (-s ^ 2 / (2 * L ^ 2))
    have hB : 0 ≤ B := Real.exp_nonneg _
    have hmeasure (N : ℕ) : μ (E N) ≤ ENNReal.ofReal B := by
      rw [← ofReal_measureReal (μ := μ) (s := E N) (by finiteness)]
      exact ENNReal.ofReal_le_ofReal (by simpa [B] using hfinite N)
    have hlim : Tendsto (fun N => μ (E N)) atTop (𝓝 (μ (⋃ N, E N))) :=
      tendsto_measure_iUnion_atTop hEmono
    have hle := le_of_tendsto hlim (Eventually.of_forall hmeasure)
    change (μ (⋃ N, E N)).toReal ≤ B
    calc
      (μ (⋃ N, E N)).toReal ≤ (ENNReal.ofReal B).toReal := ENNReal.toReal_mono (by simp) hle
      _ = B := ENNReal.toReal_ofReal hB
  have hsubset : {ω | t ≤ S ω - m} ≤ᵐ[μ] (⋃ N, E N) := by
    filter_upwards [hSupFinite] with ω hω htail
    have hpos : ∀ᶠ N in atTop, M N ω > s + m := by
      have hstrict : s + m < S ω := by dsimp [S, m] at htail; linarith [hst]
      exact (tendsto_order.mp (tendsto_gaussianRealizationPrefixMaximum X ω hω)).1
        (s + m) hstrict
    have hev : ∀ᶠ N in atTop, ω ∈ E N := by
      filter_upwards [hpos] with N hN
      dsimp [E]
      linarith
    exact Set.mem_iUnion.2 hev.exists
  calc
    μ.real {ω | t ≤ gaussianRealizationSup X ω -
        ∫ y, gaussianRealizationSup X y ∂μ} ≤ μ.real (⋃ N, E N) := by
      rw [measureReal_def, measureReal_def]
      exact ENNReal.toReal_mono (by finiteness) (measure_mono_ae hsubset)
    _ ≤ Real.exp (-s ^ 2 / (2 * L ^ 2)) := by simpa [S, m] using hUnion

/-- Sharp upper-tail concentration for the supremum of a countable centered Gaussian sequence.
Every finite prefix has a finite-dimensional standard Gaussian realization, the variables are
centered by that realization, and each variance is at most `L^2`. -/
theorem measure_centered_tail_le_of_jointlyGaussianRealizations
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) {L t : ℝ} (hL : 0 < L) (ht : 0 ≤ t)
    (hX : ∀ k, AEMeasurable (X k) μ)
    (hSupInt : Integrable (gaussianRealizationSup X) μ)
    (hSupFinite : ∀ᵐ ω ∂μ, BddAbove (Set.range fun k => X k ω))
    (hvar : ∀ k, Var[X k; μ] ≤ L ^ 2)
    (hrealize : ∀ N, ∃ a : Fin (N + 1) → Fin (N + 1) → ℝ,
      μ.map (gaussianRealizationPrefixVector X N) =
        (standardGaussianPi (N + 1)).map (gaussianRealizationLinearVector a)) :
    μ.real {ω | t ≤ gaussianRealizationSup X ω -
      ∫ y, gaussianRealizationSup X y ∂μ} ≤ Real.exp (-t ^ 2 / (2 * L ^ 2)) := by
  by_cases ht0 : t = 0
  · subst t
    calc
      μ.real {ω | 0 ≤ gaussianRealizationSup X ω -
          ∫ y, gaussianRealizationSup X y ∂μ} ≤ μ.real Set.univ :=
        measureReal_mono (Set.subset_univ _) (by finiteness)
      _ = 1 := by simp
      _ = Real.exp (-(0 : ℝ) ^ 2 / (2 * L ^ 2)) := by simp
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    let u : ℕ → ℝ := fun N => t * (1 - ((N : ℝ) + 1)⁻¹)
    have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have hden : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop := by
      apply Filter.tendsto_atTop.2
      intro b
      filter_upwards [hnat.eventually (eventually_ge_atTop (b - 1))] with N hN
      change b ≤ (N : ℝ) + 1
      linarith
    have hinv : Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hden
    have hu : Tendsto u atTop (𝓝 t) := by
      have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
      have hfactor := hconst.sub hinv
      have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => t) atTop (𝓝 t)).mul hfactor
      simpa [u] using h
    have harg : Tendsto (fun N => -(u N) ^ 2 / (2 * L ^ 2)) atTop
        (𝓝 (-t ^ 2 / (2 * L ^ 2))) := by
      have hsq := hu.pow 2
      simpa using hsq.neg.div_const (2 * L ^ 2)
    have hexp : Tendsto (fun N => Real.exp (-(u N) ^ 2 / (2 * L ^ 2))) atTop
        (𝓝 (Real.exp (-t ^ 2 / (2 * L ^ 2)))) :=
      Real.continuous_exp.continuousAt.tendsto.comp harg
    have hbound (N : ℕ) :
        μ.real {ω | t ≤ gaussianRealizationSup X ω -
          ∫ y, gaussianRealizationSup X y ∂μ} ≤
          Real.exp (-(u N) ^ 2 / (2 * L ^ 2)) := by
      have hd : ((N : ℝ) + 1)⁻¹ > 0 := inv_pos.mpr (by positivity)
      have hdle : ((N : ℝ) + 1)⁻¹ ≤ 1 := by
        rw [inv_eq_one_div]
        apply (div_le_one (by positivity)).2
        exact_mod_cast (Nat.succ_le_succ (Nat.zero_le N))
      have hu0 : 0 ≤ u N := by
        dsimp [u]
        exact mul_nonneg ht (by linarith)
      have hut : u N < t := by
        dsimp [u]
        have hfactor : 1 - ((N : ℝ) + 1)⁻¹ < 1 := by linarith
        nlinarith [htpos, hfactor]
      exact measure_centered_tail_le_of_jointlyGaussianRealizations_below
        μ X hL hu0 hut hX hSupInt hSupFinite hvar hrealize
    exact ge_of_tendsto hexp (Eventually.of_forall hbound)

end ASDExplicitGamma.Gaussian
