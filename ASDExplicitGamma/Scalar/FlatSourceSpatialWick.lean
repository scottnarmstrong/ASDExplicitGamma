module

public import ASDExplicitGamma.Scalar.FlatSourceGaussianWick

/-! The finite-mode Wick contraction for a spatially varying scalar source. -/

@[expose] public section

open MeasureTheory
open ASDExplicitGamma.Gaussian
open ProbabilityTheory
open scoped ENNReal

namespace ASDExplicitGamma.Scalar

/-- Integrating the pointwise finite-mode Wick estimate preserves the factor
three when the scalar mode variance is bounded uniformly in space. The vector
modes are only required to have their actual spatial `L²` regularity. -/
theorem flat_source_finite_mode_spatial_product_bound
    {X : Type*} [MeasurableSpace X]
    (ν : Measure X) (N : ℕ)
    (a : ℕ → X → ℝ) (b : Fin 2 → ℕ → X → ℝ)
    (A : ℝ)
    (haMeas : ∀ n, Measurable (a n))
    (ha : ∀ x, ∑ n ∈ Finset.range N, (a n x) ^ 2 ≤ A)
    (hb : ∀ i n, MemLp (b i n) 2 ν)
    :
    (∫ x, ∫ ω,
      (gaussianScalarPartialSum (fun n => a n x) N ω) ^ 2 *
        (∑ i : Fin 2,
          (gaussianScalarPartialSum (fun n => b i n x) N ω) ^ 2)
      ∂standardGaussianInfinitePi ∂ν) ≤
      3 * A * (∑ i : Fin 2, ∑ n ∈ Finset.range N,
        ∫ x, (b i n x) ^ 2 ∂ν) := by
  let g : X → ℝ := fun x =>
    ∫ ω, (gaussianScalarPartialSum (fun n => a n x) N ω) ^ 2 *
      (∑ i : Fin 2,
        (gaussianScalarPartialSum (fun n => b i n x) N ω) ^ 2)
      ∂standardGaussianInfinitePi
  let s : X → ℝ := fun x =>
    ∑ i : Fin 2, ∑ n ∈ Finset.range N, (b i n x) ^ 2
  have hjoint : AEStronglyMeasurable
      (fun z : X × (ℕ → ℝ) =>
        (gaussianScalarPartialSum (fun n => a n z.1) N z.2) ^ 2 *
          (∑ i : Fin 2,
            (gaussianScalarPartialSum (fun n => b i n z.1) N z.2) ^ 2))
      (ν.prod standardGaussianInfinitePi) := by
    have hω (n : ℕ) : AEStronglyMeasurable
        (fun z : X × (ℕ → ℝ) => z.2 n) (ν.prod standardGaussianInfinitePi) :=
      ((measurable_pi_apply n).comp measurable_snd).aestronglyMeasurable
    have ha' (n : ℕ) : AEStronglyMeasurable
        (fun z : X × (ℕ → ℝ) => a n z.1) (ν.prod standardGaussianInfinitePi) :=
      (haMeas n).aestronglyMeasurable.comp_fst
    have hb' (i : Fin 2) (n : ℕ) : AEStronglyMeasurable
        (fun z : X × (ℕ → ℝ) => b i n z.1) (ν.prod standardGaussianInfinitePi) :=
      (hb i n).aestronglyMeasurable.comp_fst
    have hscalar : AEStronglyMeasurable
        (fun z : X × (ℕ → ℝ) =>
          gaussianScalarPartialSum (fun n => a n z.1) N z.2)
        (ν.prod standardGaussianInfinitePi) := by
      unfold gaussianScalarPartialSum
      exact Finset.aestronglyMeasurable_fun_sum (Finset.range N) fun n hn =>
        (hω n).mul (ha' n)
    have hvector (i : Fin 2) : AEStronglyMeasurable
        (fun z : X × (ℕ → ℝ) =>
          gaussianScalarPartialSum (fun n => b i n z.1) N z.2)
        (ν.prod standardGaussianInfinitePi) := by
      unfold gaussianScalarPartialSum
      exact Finset.aestronglyMeasurable_fun_sum (Finset.range N) fun n hn =>
        (hω n).mul (hb' i n)
    have hvectorSq : AEStronglyMeasurable
        (fun z : X × (ℕ → ℝ) => ∑ i : Fin 2,
          (gaussianScalarPartialSum (fun n => b i n z.1) N z.2) ^ 2)
        (ν.prod standardGaussianInfinitePi) :=
      Finset.aestronglyMeasurable_fun_sum Finset.univ fun i hi =>
        (hvector i).pow 2
    exact (hscalar.pow 2).mul hvectorSq
  have hmeas : AEStronglyMeasurable (fun x =>
      ∫ ω, (gaussianScalarPartialSum (fun n => a n x) N ω) ^ 2 *
        (∑ i : Fin 2,
          (gaussianScalarPartialSum (fun n => b i n x) N ω) ^ 2)
        ∂standardGaussianInfinitePi) ν := by
    simpa only [Function.uncurry_apply_pair] using hjoint.integral_prod_right'
  have hsTerm (i : Fin 2) (n : ℕ) :
      Integrable (fun x => (b i n x) ^ 2) ν := by
    exact (hb i n).integrable_sq
  have hs : Integrable s ν := by
    dsimp [s]
    apply integrable_finsetSum Finset.univ
    intro i hi
    apply integrable_finsetSum (Finset.range N)
    intro n hn
    exact hsTerm i n
  have hright : Integrable (fun x => (3 * A) * s x) ν := hs.const_mul (3 * A)
  have hpoint (x : X) : g x ≤ (3 * A) * s x := by
    have hw := centered_gaussian_finite_mode_product_bound N
      (fun n => a n x) (fun i n => b i n x)
    have hfactor :
        (∑ n ∈ Finset.range N, (a n x) ^ 2) ≤ A := ha x
    have hsx : 0 ≤ s x := by
      dsimp [s]
      exact Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun n hn => sq_nonneg _
    calc
      g x ≤ 3 * (∑ n ∈ Finset.range N, (a n x) ^ 2) * s x := by
        simpa [g, s] using hw
      _ ≤ (3 * A) * s x := by
        calc
          _ = (3 * (∑ n ∈ Finset.range N, (a n x) ^ 2)) * s x := by ring
          _ ≤ (3 * A) * s x :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hfactor (by norm_num)) hsx
  have hg0 (x : X) : 0 ≤ g x := by
    dsimp [g]
    apply integral_nonneg
    intro ω
    apply mul_nonneg
    · exact sq_nonneg _
    · exact Finset.sum_nonneg fun i hi => sq_nonneg _
  have hleft : Integrable g ν := by
    apply hright.mono' hmeas
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 x)]
    exact hpoint x
  calc
    _ = ∫ x, g x ∂ν := rfl
    _ ≤ ∫ x, (3 * A) * s x ∂ν := integral_mono hleft hright hpoint
    _ = 3 * A * (∑ i : Fin 2, ∑ n ∈ Finset.range N,
        ∫ x, (b i n x) ^ 2 ∂ν) := by
      simp only [s, integral_const_mul]
      congr 1
      rw [integral_finsetSum Finset.univ (fun i hi => by
        apply integrable_finsetSum (Finset.range N)
        intro n hn
        exact hsTerm i n)]
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_finsetSum (Finset.range N) (fun n hn => hsTerm i n)]

/- The integrability upgrade to the estimate above is useful when a spatial
L² norm itself is averaged over the Gaussian sample: it permits a genuine
Fubini swap rather than a change in the order of two nonnegative integrals. -/
theorem flat_source_finite_mode_spatial_product_integral_swap
    {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] (N : ℕ)
    (a : ℕ → X → ℝ) (b : Fin 2 → ℕ → X → ℝ)
    (A : ℝ)
    (haMeas : ∀ n, Measurable (a n))
    (ha : ∀ x, ∑ n ∈ Finset.range N, (a n x) ^ 2 ≤ A)
    (hb : ∀ i n, MemLp (b i n) 2 ν) :
    Integrable (fun ω => ∫ x,
      (gaussianScalarPartialSum (fun n => a n x) N ω) ^ 2 *
        ∑ i : Fin 2,
          (gaussianScalarPartialSum (fun n => b i n x) N ω) ^ 2
      ∂ν) standardGaussianInfinitePi ∧
    (∫ x, ∫ ω,
      (gaussianScalarPartialSum (fun n => a n x) N ω) ^ 2 *
        ∑ i : Fin 2,
          (gaussianScalarPartialSum (fun n => b i n x) N ω) ^ 2
      ∂standardGaussianInfinitePi ∂ν) =
    (∫ ω, ∫ x,
      (gaussianScalarPartialSum (fun n => a n x) N ω) ^ 2 *
        ∑ i : Fin 2,
          (gaussianScalarPartialSum (fun n => b i n x) N ω) ^ 2
      ∂ν ∂standardGaussianInfinitePi) := by
  have instHolderFourFourTwo : ENNReal.HolderTriple 4 4 2 := ⟨by
    rw [show (4:ℝ≥0∞) = 2*2 by norm_num, ENNReal.mul_inv, ← add_mul,
      ENNReal.inv_two_add_inv_two, one_mul] <;> norm_num⟩
  let F : X × (ℕ → ℝ) → ℝ := fun z =>
    (gaussianScalarPartialSum (fun n => a n z.1) N z.2) ^ 2 *
      ∑ i : Fin 2,
        (gaussianScalarPartialSum (fun n => b i n z.1) N z.2) ^ 2
  let g : X → ℝ := fun x =>
    ∫ ω, (gaussianScalarPartialSum (fun n => a n x) N ω) ^ 2 *
      ∑ i : Fin 2,
        (gaussianScalarPartialSum (fun n => b i n x) N ω) ^ 2
      ∂standardGaussianInfinitePi
  let s : X → ℝ := fun x =>
    ∑ i : Fin 2, ∑ n ∈ Finset.range N, (b i n x) ^ 2
  have hjoint : AEStronglyMeasurable F
      (ν.prod standardGaussianInfinitePi) := by
    have hω (n : ℕ) : AEStronglyMeasurable
        (fun z : X × (ℕ → ℝ) => z.2 n) (ν.prod standardGaussianInfinitePi) :=
      ((measurable_pi_apply n).comp measurable_snd).aestronglyMeasurable
    have ha' (n : ℕ) : AEStronglyMeasurable
        (fun z : X × (ℕ → ℝ) => a n z.1) (ν.prod standardGaussianInfinitePi) :=
      (haMeas n).aestronglyMeasurable.comp_fst
    have hb' (i : Fin 2) (n : ℕ) : AEStronglyMeasurable
        (fun z : X × (ℕ → ℝ) => b i n z.1) (ν.prod standardGaussianInfinitePi) :=
      (hb i n).aestronglyMeasurable.comp_fst
    have hscalar : AEStronglyMeasurable
        (fun z : X × (ℕ → ℝ) =>
          gaussianScalarPartialSum (fun n => a n z.1) N z.2)
        (ν.prod standardGaussianInfinitePi) := by
      unfold gaussianScalarPartialSum
      exact Finset.aestronglyMeasurable_fun_sum (Finset.range N) fun n hn =>
        (hω n).mul (ha' n)
    have hvector (i : Fin 2) : AEStronglyMeasurable
        (fun z : X × (ℕ → ℝ) =>
          gaussianScalarPartialSum (fun n => b i n z.1) N z.2)
        (ν.prod standardGaussianInfinitePi) := by
      unfold gaussianScalarPartialSum
      exact Finset.aestronglyMeasurable_fun_sum (Finset.range N) fun n hn =>
        (hω n).mul (hb' i n)
    have hvectorSq : AEStronglyMeasurable
        (fun z : X × (ℕ → ℝ) => ∑ i : Fin 2,
          (gaussianScalarPartialSum (fun n => b i n z.1) N z.2) ^ 2)
        (ν.prod standardGaussianInfinitePi) :=
      Finset.aestronglyMeasurable_fun_sum Finset.univ fun i hi =>
        (hvector i).pow 2
    exact (hscalar.pow 2).mul hvectorSq
  have hsection (x : X) : Integrable (fun ω => F (x, ω))
      standardGaussianInfinitePi := by
    let X₀ := gaussianScalarPartialSum (fun n => a n x) N
    let Y₀ (i : Fin 2) := gaussianScalarPartialSum (fun n => b i n x) N
    have hmX : AEMeasurable X₀ standardGaussianInfinitePi := by
      unfold X₀ gaussianScalarPartialSum
      exact (Finset.measurable_sum _ fun n hn =>
        (measurable_pi_apply n).mul measurable_const).aemeasurable
    have hXlaw : HasGaussianLaw X₀ standardGaussianInfinitePi := by
      exact ⟨hmX, by
        dsimp [X₀]
        rw [map_gaussianScalarPartialSum]
        infer_instance⟩
    have hX4 : MemLp X₀ 4 standardGaussianInfinitePi :=
      hXlaw.memLp (by norm_num)
    have hX2 : MemLp (fun ω => (X₀ ω) ^ 2) 2
        standardGaussianInfinitePi := by
      simpa only [pow_two] using hX4.fun_mul hX4
    have hY4 (i : Fin 2) : MemLp (Y₀ i) 4 standardGaussianInfinitePi := by
      have hmY : AEMeasurable (Y₀ i) standardGaussianInfinitePi := by
        unfold Y₀ gaussianScalarPartialSum
        exact (Finset.measurable_sum _ fun n hn =>
          (measurable_pi_apply n).mul measurable_const).aemeasurable
      have hYlaw : HasGaussianLaw (Y₀ i) standardGaussianInfinitePi := by
        exact ⟨hmY, by
          dsimp [Y₀]
          rw [map_gaussianScalarPartialSum]
          infer_instance⟩
      exact hYlaw.memLp (by norm_num)
    have hY2 (i : Fin 2) : MemLp (fun ω => (Y₀ i ω) ^ 2) 2
        standardGaussianInfinitePi := by
      simpa only [pow_two] using (hY4 i).fun_mul (hY4 i)
    have hterm (i : Fin 2) : Integrable
        (fun ω => (X₀ ω) ^ 2 * (Y₀ i ω) ^ 2) standardGaussianInfinitePi :=
      hX2.integrable_mul (hY2 i)
    have hsum : Integrable
        (fun ω => ∑ i : Fin 2, (X₀ ω) ^ 2 * (Y₀ i ω) ^ 2)
        standardGaussianInfinitePi :=
      integrable_finsetSum Finset.univ fun i hi => hterm i
    change Integrable (fun ω => X₀ ω ^ 2 * ∑ i : Fin 2, (Y₀ i ω) ^ 2)
      standardGaussianInfinitePi
    convert hsum using 1
    funext ω
    rw [Finset.mul_sum]
  have hmeas : AEStronglyMeasurable g ν := by
    simpa only [Function.uncurry_apply_pair, F, g] using
      hjoint.integral_prod_right'
  have hsTerm (i : Fin 2) (n : ℕ) :
      Integrable (fun x => (b i n x) ^ 2) ν := (hb i n).integrable_sq
  have hs : Integrable s ν := by
    dsimp [s]
    apply integrable_finsetSum Finset.univ
    intro i hi
    apply integrable_finsetSum (Finset.range N)
    intro n hn
    exact hsTerm i n
  have hright : Integrable (fun x => (3 * A) * s x) ν :=
    hs.const_mul (3 * A)
  have hpoint (x : X) : g x ≤ (3 * A) * s x := by
    have hw := centered_gaussian_finite_mode_product_bound N
      (fun n => a n x) (fun i n => b i n x)
    have hfactor : ∑ n ∈ Finset.range N, (a n x) ^ 2 ≤ A := ha x
    have hsx : 0 ≤ s x := by
      dsimp [s]
      exact Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun n hn => sq_nonneg _
    calc
      g x ≤ 3 * (∑ n ∈ Finset.range N, (a n x) ^ 2) * s x := by
        simpa [g, s] using hw
      _ ≤ (3 * A) * s x := by
        calc
          _ = (3 * (∑ n ∈ Finset.range N, (a n x) ^ 2)) * s x := by ring
          _ ≤ (3 * A) * s x :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hfactor (by norm_num)) hsx
  have hg0 (x : X) : 0 ≤ g x := by
    dsimp [g]
    apply integral_nonneg
    intro ω
    apply mul_nonneg
    · exact sq_nonneg _
    · exact Finset.sum_nonneg fun i hi => sq_nonneg _
  have hleft : Integrable g ν := by
    apply hright.mono' hmeas
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 x)]
    exact hpoint x
  have hnormEq (x : X) :
      (∫ ω, ‖F (x, ω)‖ ∂standardGaussianInfinitePi) = g x := by
    apply integral_congr_ae
    filter_upwards [] with ω
    have hFnonneg : 0 ≤ F (x, ω) := by
      dsimp [F]
      exact mul_nonneg (sq_nonneg _) <|
        Finset.sum_nonneg fun i hi => sq_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hFnonneg]
  have hnormIntegrable : Integrable
      (fun x => ∫ ω, ‖F (x, ω)‖ ∂standardGaussianInfinitePi) ν := by
    exact hleft.congr (ae_of_all ν fun x => (hnormEq x).symm)
  have hprod : Integrable F (ν.prod standardGaussianInfinitePi) :=
    (integrable_prod_iff hjoint).2
      ⟨Filter.Eventually.of_forall hsection, hnormIntegrable⟩
  have hprod' : Integrable (Function.uncurry (fun x ω => F (x, ω)))
      (ν.prod standardGaussianInfinitePi) := by
    convert hprod using 1
    funext z
    cases z
    rfl
  have hswap := integral_integral_swap
    (f := fun x ω => F (x, ω))
    hprod'
  have houter : Integrable (fun ω => ∫ x, F (x, ω) ∂ν)
      standardGaussianInfinitePi := by
    simpa only [F] using hprod.integral_prod_right
  refine ⟨?_, ?_⟩
  · simpa only [F] using houter
  · change (∫ x, ∫ ω, F (x, ω) ∂standardGaussianInfinitePi ∂ν) =
      ∫ ω, ∫ x, F (x, ω) ∂ν ∂standardGaussianInfinitePi
    exact hswap

/-- A finite common-noise scalar-times-vector product obeys an integrated
weak-gradient bound. The derivative families and the original factors use
the same Gaussian coordinates. -/
theorem flat_source_finite_mode_spatial_gradient_bound
    {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] (N : ℕ)
    (a : ℕ → X → ℝ) (da : Fin 2 → ℕ → X → ℝ)
    (b : Fin 2 → ℕ → X → ℝ) (db : Fin 2 → Fin 2 → ℕ → X → ℝ)
    (A AD : ℝ)
    (haMeas : ∀ n, Measurable (a n))
    (hdaMeas : ∀ i n, Measurable (da i n))
    (ha : ∀ x, ∑ n ∈ Finset.range N, (a n x) ^ 2 ≤ A)
    (hda : ∀ x, ∑ i : Fin 2, ∑ n ∈ Finset.range N,
      (da i n x) ^ 2 ≤ AD)
    (hb : ∀ i n, MemLp (b i n) 2 ν)
    (hdb : ∀ i j n, MemLp (db i j n) 2 ν) :
    Integrable (fun ω => ∫ x,
      ∑ i : Fin 2, ∑ j : Fin 2,
        (gaussianScalarPartialSum (fun n => da j n x) N ω *
            gaussianScalarPartialSum (fun n => b i n x) N ω +
          gaussianScalarPartialSum (fun n => a n x) N ω *
            gaussianScalarPartialSum (fun n => db i j n x) N ω) ^ 2
      ∂ν) standardGaussianInfinitePi ∧
    (∫ ω, ∫ x,
      ∑ i : Fin 2, ∑ j : Fin 2,
        (gaussianScalarPartialSum (fun n => da j n x) N ω *
            gaussianScalarPartialSum (fun n => b i n x) N ω +
          gaussianScalarPartialSum (fun n => a n x) N ω *
            gaussianScalarPartialSum (fun n => db i j n x) N ω) ^ 2
      ∂ν ∂standardGaussianInfinitePi) ≤
      6 * AD * (∑ i : Fin 2, ∑ n ∈ Finset.range N,
        ∫ x, (b i n x) ^ 2 ∂ν) +
      6 * A * (∑ i : Fin 2, ∑ j : Fin 2, ∑ n ∈ Finset.range N,
        ∫ x, (db i j n x) ^ 2 ∂ν) := by
  let F : X × (ℕ → ℝ) → ℝ := fun z =>
    ∑ i : Fin 2, ∑ j : Fin 2,
      (gaussianScalarPartialSum (fun n => da j n z.1) N z.2 *
          gaussianScalarPartialSum (fun n => b i n z.1) N z.2 +
        gaussianScalarPartialSum (fun n => a n z.1) N z.2 *
          gaussianScalarPartialSum (fun n => db i j n z.1) N z.2) ^ 2
  let g : X → ℝ := fun x => ∫ ω, F (x, ω) ∂standardGaussianInfinitePi
  let sB : X → ℝ := fun x =>
    ∑ i : Fin 2, ∑ n ∈ Finset.range N, (b i n x) ^ 2
  let sDB : X → ℝ := fun x =>
    ∑ i : Fin 2, ∑ j : Fin 2, ∑ n ∈ Finset.range N, (db i j n x) ^ 2
  have hω (n : ℕ) : AEStronglyMeasurable
      (fun z : X × (ℕ → ℝ) => z.2 n) (ν.prod standardGaussianInfinitePi) :=
    ((measurable_pi_apply n).comp measurable_snd).aestronglyMeasurable
  have ha' (n : ℕ) : AEStronglyMeasurable
      (fun z : X × (ℕ → ℝ) => a n z.1) (ν.prod standardGaussianInfinitePi) :=
    (haMeas n).aestronglyMeasurable.comp_fst
  have hda' (i : Fin 2) (n : ℕ) : AEStronglyMeasurable
      (fun z : X × (ℕ → ℝ) => da i n z.1) (ν.prod standardGaussianInfinitePi) :=
    (hdaMeas i n).aestronglyMeasurable.comp_fst
  have hb' (i : Fin 2) (n : ℕ) : AEStronglyMeasurable
      (fun z : X × (ℕ → ℝ) => b i n z.1) (ν.prod standardGaussianInfinitePi) :=
    (hb i n).aestronglyMeasurable.comp_fst
  have hdb' (i j : Fin 2) (n : ℕ) : AEStronglyMeasurable
      (fun z : X × (ℕ → ℝ) => db i j n z.1) (ν.prod standardGaussianInfinitePi) :=
    (hdb i j n).aestronglyMeasurable.comp_fst
  have hscalar (f : ℕ → X → ℝ)
      (hf : ∀ n, AEStronglyMeasurable
        (fun z : X × (ℕ → ℝ) => f n z.1) (ν.prod standardGaussianInfinitePi)) :
      AEStronglyMeasurable
        (fun z : X × (ℕ → ℝ) => gaussianScalarPartialSum
          (fun n => f n z.1) N z.2) (ν.prod standardGaussianInfinitePi) := by
    unfold gaussianScalarPartialSum
    exact Finset.aestronglyMeasurable_fun_sum (Finset.range N) fun n hn =>
      (hω n).mul (hf n)
  have hprod (i j : Fin 2) : AEStronglyMeasurable
      (fun z : X × (ℕ → ℝ) =>
        (gaussianScalarPartialSum (fun n => da j n z.1) N z.2 *
            gaussianScalarPartialSum (fun n => b i n z.1) N z.2 +
          gaussianScalarPartialSum (fun n => a n z.1) N z.2 *
            gaussianScalarPartialSum (fun n => db i j n z.1) N z.2) ^ 2)
      (ν.prod standardGaussianInfinitePi) := by
    have hfirst := (hscalar (fun n x => da j n x) (hda' j)).mul
      (hscalar (fun n x => b i n x) (hb' i))
    have hsecond := (hscalar a ha').mul
      (hscalar (fun n x => db i j n x) (fun n => hdb' i j n))
    exact (hfirst.add hsecond).pow 2
  have hjoint : AEStronglyMeasurable F (ν.prod standardGaussianInfinitePi) := by
    dsimp [F]
    exact Finset.aestronglyMeasurable_fun_sum Finset.univ fun i hi =>
      Finset.aestronglyMeasurable_fun_sum Finset.univ fun j hj => hprod i j
  have hmeas : AEStronglyMeasurable g ν := by
    simpa only [Function.uncurry_apply_pair, F, g] using hjoint.integral_prod_right'
  have hbSq (i : Fin 2) (n : ℕ) :
      Integrable (fun x => (b i n x) ^ 2) ν := (hb i n).integrable_sq
  have hdbSq (i j : Fin 2) (n : ℕ) :
      Integrable (fun x => (db i j n x) ^ 2) ν := (hdb i j n).integrable_sq
  have hsB : Integrable sB ν := by
    dsimp [sB]
    apply integrable_finsetSum Finset.univ
    intro i hi
    apply integrable_finsetSum (Finset.range N)
    intro n hn
    exact hbSq i n
  have hsDB : Integrable sDB ν := by
    dsimp [sDB]
    apply integrable_finsetSum Finset.univ
    intro i hi
    apply integrable_finsetSum Finset.univ
    intro j hj
    apply integrable_finsetSum (Finset.range N)
    intro n hn
    exact hdbSq i j n
  have hright : Integrable (fun x => (6 * AD) * sB x + (6 * A) * sDB x) ν := by
    exact (hsB.const_mul (6 * AD)).add (hsDB.const_mul (6 * A))
  have hg0 (x : X) : 0 ≤ g x := by
    dsimp [g, F]
    apply integral_nonneg
    intro ω
    exact Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj => sq_nonneg _
  have hwick (x : X) (i j : Fin 2) :
      Integrable (fun ω =>
        (gaussianScalarPartialSum (fun n => da j n x) N ω *
            gaussianScalarPartialSum (fun n => b i n x) N ω +
          gaussianScalarPartialSum (fun n => a n x) N ω *
            gaussianScalarPartialSum (fun n => db i j n x) N ω) ^ 2)
        standardGaussianInfinitePi ∧
      (∫ ω,
        (gaussianScalarPartialSum (fun n => da j n x) N ω *
            gaussianScalarPartialSum (fun n => b i n x) N ω +
          gaussianScalarPartialSum (fun n => a n x) N ω *
            gaussianScalarPartialSum (fun n => db i j n x) N ω) ^ 2
        ∂standardGaussianInfinitePi) ≤
        6 * (∑ n ∈ Finset.range N, (da j n x) ^ 2) *
            (∑ n ∈ Finset.range N, (b i n x) ^ 2) +
          6 * (∑ n ∈ Finset.range N, (a n x) ^ 2) *
            (∑ n ∈ Finset.range N, (db i j n x) ^ 2) :=
    centered_gaussian_finite_mode_product_gradient_component_bound_auto
      N (fun n => a n x) (fun n => b i n x)
        (fun n => da j n x) (fun n => db i j n x)
  have hg_sum (x : X) : g x =
      ∑ i : Fin 2, ∑ j : Fin 2,
        ∫ ω,
          (gaussianScalarPartialSum (fun n => da j n x) N ω *
              gaussianScalarPartialSum (fun n => b i n x) N ω +
            gaussianScalarPartialSum (fun n => a n x) N ω *
              gaussianScalarPartialSum (fun n => db i j n x) N ω) ^ 2
          ∂standardGaussianInfinitePi := by
    dsimp [g, F]
    rw [integral_finsetSum Finset.univ fun i hi =>
      integrable_finsetSum Finset.univ fun j hj => (hwick x i j).1]
    congr 1
    funext i
    rw [integral_finsetSum Finset.univ fun j hj => (hwick x i j).1]
  have hpoint (x : X) : g x ≤ (6 * AD) * sB x + (6 * A) * sDB x := by
    rw [hg_sum x]
    dsimp [sB, sDB]
    calc
      _ ≤ ∑ i : Fin 2, ∑ j : Fin 2,
          (6 * (∑ n ∈ Finset.range N, (da j n x) ^ 2) *
              (∑ n ∈ Finset.range N, (b i n x) ^ 2) +
            6 * (∑ n ∈ Finset.range N, (a n x) ^ 2) *
              (∑ n ∈ Finset.range N, (db i j n x) ^ 2)) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact (hwick x i j).2
      _ = 6 * (∑ j : Fin 2, ∑ n ∈ Finset.range N,
            (da j n x) ^ 2) *
            (∑ i : Fin 2, ∑ n ∈ Finset.range N, (b i n x) ^ 2) +
          6 * (∑ n ∈ Finset.range N, (a n x) ^ 2) *
            (∑ i : Fin 2, ∑ j : Fin 2,
              ∑ n ∈ Finset.range N, (db i j n x) ^ 2) := by
        let dvar : Fin 2 → ℝ := fun j =>
          ∑ n ∈ Finset.range N, (da j n x) ^ 2
        let bvar : Fin 2 → ℝ := fun i =>
          ∑ n ∈ Finset.range N, (b i n x) ^ 2
        let aval : ℝ := ∑ n ∈ Finset.range N, (a n x) ^ 2
        let dbvar : Fin 2 → Fin 2 → ℝ := fun i j =>
          ∑ n ∈ Finset.range N, (db i j n x) ^ 2
        have hfirst : (∑ i : Fin 2, ∑ j : Fin 2,
            6 * dvar j * bvar i) =
            6 * (∑ j : Fin 2, dvar j) * (∑ i : Fin 2, bvar i) := by
          calc
            _ = ∑ i : Fin 2, 6 * (∑ j : Fin 2, dvar j * bvar i) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j hj
              ring
            _ = 6 * (∑ i : Fin 2, ∑ j : Fin 2, dvar j * bvar i) := by
              rw [Finset.mul_sum]
            _ = 6 * ((∑ j : Fin 2, dvar j) * (∑ i : Fin 2, bvar i)) := by
              congr 1
              rw [Finset.sum_comm]
              exact (Finset.sum_mul_sum _ _ _ _).symm
            _ = (6 * (∑ j : Fin 2, dvar j)) * (∑ i : Fin 2, bvar i) := by ring
        have hsecond : (∑ i : Fin 2, ∑ j : Fin 2,
            6 * aval * dbvar i j) =
            6 * aval * (∑ i : Fin 2, ∑ j : Fin 2, dbvar i j) := by
          calc
            _ = ∑ i : Fin 2, (6 * aval) * (∑ j : Fin 2, dbvar i j) := by
              apply Finset.sum_congr rfl
              intro i hi
              exact (Finset.mul_sum Finset.univ (fun j : Fin 2 => dbvar i j)
                (6 * aval)).symm
            _ = (6 * aval) * (∑ i : Fin 2, ∑ j : Fin 2, dbvar i j) := by
              exact (Finset.mul_sum Finset.univ
                (fun i : Fin 2 => ∑ j : Fin 2, dbvar i j) (6 * aval)).symm
        simp only [Finset.sum_add_distrib]
        change (∑ i : Fin 2, ∑ j : Fin 2, 6 * dvar j * bvar i) +
            (∑ i : Fin 2, ∑ j : Fin 2, 6 * aval * dbvar i j) =
          6 * (∑ j : Fin 2, dvar j) * (∑ i : Fin 2, bvar i) +
            6 * aval * (∑ i : Fin 2, ∑ j : Fin 2, dbvar i j)
        rw [hfirst, hsecond]
      _ ≤ (6 * AD) * sB x + (6 * A) * sDB x := by
        have hBnonneg : 0 ≤ sB x :=
          Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun n hn => sq_nonneg _
        have hdbnonneg : 0 ≤ sDB x :=
          Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj =>
            Finset.sum_nonneg fun n hn => sq_nonneg _
        have hda := hda x
        have ha := ha x
        nlinarith [mul_le_mul_of_nonneg_right hda hBnonneg,
          mul_le_mul_of_nonneg_right ha hdbnonneg]
  have hleft : Integrable g ν := by
    apply hright.mono' hmeas
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 x)]
    exact hpoint x
  have hbound : (∫ x, ∫ ω,
      ∑ i : Fin 2, ∑ j : Fin 2,
        (gaussianScalarPartialSum (fun n => da j n x) N ω *
            gaussianScalarPartialSum (fun n => b i n x) N ω +
          gaussianScalarPartialSum (fun n => a n x) N ω *
            gaussianScalarPartialSum (fun n => db i j n x) N ω) ^ 2
      ∂standardGaussianInfinitePi ∂ν) ≤
      6 * AD * (∑ i : Fin 2, ∑ n ∈ Finset.range N,
        ∫ x, (b i n x) ^ 2 ∂ν) +
      6 * A * (∑ i : Fin 2, ∑ j : Fin 2, ∑ n ∈ Finset.range N,
        ∫ x, (db i j n x) ^ 2 ∂ν) := by
   calc
    _ = ∫ x, g x ∂ν := rfl
    _ ≤ ∫ x, (6 * AD) * sB x + (6 * A) * sDB x ∂ν :=
      integral_mono hleft hright hpoint
    _ = 6 * AD * (∑ i : Fin 2, ∑ n ∈ Finset.range N,
          ∫ x, (b i n x) ^ 2 ∂ν) +
        6 * A * (∑ i : Fin 2, ∑ j : Fin 2, ∑ n ∈ Finset.range N,
          ∫ x, (db i j n x) ^ 2 ∂ν) := by
      rw [integral_add (hsB.const_mul (6 * AD)) (hsDB.const_mul (6 * A)),
        integral_const_mul, integral_const_mul]
      congr 2
      · rw [integral_finsetSum Finset.univ (fun i hi =>
          integrable_finsetSum (Finset.range N) (fun n hn => hbSq i n))]
        apply Finset.sum_congr rfl
        intro i hi
        rw [integral_finsetSum (Finset.range N) (fun n hn => hbSq i n)]
      · rw [integral_finsetSum Finset.univ (fun i hi =>
          integrable_finsetSum Finset.univ (fun j hj =>
            integrable_finsetSum (Finset.range N) (fun n hn => hdbSq i j n)))]
        apply Finset.sum_congr rfl
        intro i hi
        rw [integral_finsetSum Finset.univ (fun j hj =>
          integrable_finsetSum (Finset.range N) (fun n hn => hdbSq i j n))]
        apply Finset.sum_congr rfl
        intro j hj
        rw [integral_finsetSum (Finset.range N) (fun n hn => hdbSq i j n)]
  have hsection (x : X) : Integrable (fun ω => F (x, ω))
      standardGaussianInfinitePi := by
    dsimp [F]
    apply integrable_finsetSum Finset.univ
    intro i hi
    apply integrable_finsetSum Finset.univ
    intro j hj
    exact (hwick x i j).1
  have hnormEq (x : X) :
      (∫ ω, ‖F (x, ω)‖ ∂standardGaussianInfinitePi) = g x := by
    apply integral_congr_ae
    filter_upwards [] with ω
    have hFnonneg : 0 ≤ F (x, ω) := by
      dsimp [F]
      exact Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj => sq_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hFnonneg]
  have hnormIntegrable : Integrable
      (fun x => ∫ ω, ‖F (x, ω)‖ ∂standardGaussianInfinitePi) ν := by
    exact hleft.congr (ae_of_all ν fun x => (hnormEq x).symm)
  have hprod : Integrable F (ν.prod standardGaussianInfinitePi) :=
    (integrable_prod_iff hjoint).2
      ⟨Filter.Eventually.of_forall hsection, hnormIntegrable⟩
  have hprod' : Integrable (Function.uncurry (fun x ω => F (x, ω)))
      (ν.prod standardGaussianInfinitePi) := by
    convert hprod using 1
    funext z
    cases z
    rfl
  have hswap := integral_integral_swap
    (f := fun x ω => F (x, ω)) hprod'
  have houter : Integrable (fun ω => ∫ x, F (x, ω) ∂ν)
      standardGaussianInfinitePi := by
    simpa only [F] using hprod.integral_prod_right
  refine ⟨?_, ?_⟩
  · simpa only [F] using houter
  · calc
      _ = ∫ x, ∫ ω,
          ∑ i : Fin 2, ∑ j : Fin 2,
            (gaussianScalarPartialSum (fun n => da j n x) N ω *
                gaussianScalarPartialSum (fun n => b i n x) N ω +
              gaussianScalarPartialSum (fun n => a n x) N ω *
                gaussianScalarPartialSum (fun n => db i j n x) N ω) ^ 2
          ∂standardGaussianInfinitePi ∂ν := hswap.symm
      _ ≤ _ := hbound

end ASDExplicitGamma.Scalar
