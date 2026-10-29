module

public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Sym.Card
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.IdentDistrib
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
public import Homogenization.Probability.IndependentSums.Rosenthal.ProductDifference
public import Homogenization.Probability.IndependentSums.Rosenthal.Symmetrization

/-! # Finite even-moment averaging -/

@[expose] public section

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

namespace ASDExplicitGamma.AllOrder

private theorem nat_pow_le_three_pow_mul_factorial (q : ℕ) :
    (q : ℝ) ^ q ≤ 3 ^ q * q.factorial := by
  induction q with
  | zero => norm_num
  | succ n ih =>
      by_cases hn : n = 0
      · subst n
        norm_num
      have hratio : ((n + 1 : ℕ) : ℝ) ^ (n + 1) =
          (n + 1 : ℝ) * (1 + (n : ℝ)⁻¹) ^ n * (n : ℝ) ^ n := by
        have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
        have hbase : (n + 1 : ℝ) = (n : ℝ) * (1 + (n : ℝ)⁻¹) := by
          field_simp
        calc
          ((n + 1 : ℕ) : ℝ) ^ (n + 1) =
              ((n + 1 : ℝ) ^ n) * (n + 1 : ℝ) := by
                have hncast : ((n + 1 : ℕ) : ℝ) = (n + 1 : ℝ) := by norm_num
                rw [hncast, pow_succ]
          _ = ((n : ℝ) * (1 + (n : ℝ)⁻¹)) ^ n * (n + 1 : ℝ) := by rw [hbase]
          _ = (n + 1 : ℝ) * (1 + (n : ℝ)⁻¹) ^ n * (n : ℝ) ^ n := by
            rw [mul_pow]
            ring
      have hsmall : (1 + (n : ℝ)⁻¹) ^ n ≤ 3 :=
        (Real.one_add_inv_pow_le_exp (n := n)).trans Real.exp_one_lt_three.le
      calc
        ((n + 1 : ℕ) : ℝ) ^ (n + 1) =
            (n + 1 : ℝ) * (1 + (n : ℝ)⁻¹) ^ n * (n : ℝ) ^ n := hratio
        _ ≤
            (n + 1 : ℝ) * 3 * (n : ℝ) ^ n := by gcongr
        _ ≤ (3 : ℝ) ^ n * (n.factorial : ℝ) * (n + 1 : ℝ) * 3 := by
          have hmul := mul_le_mul_of_nonneg_left ih
            (mul_nonneg (by positivity : 0 ≤ (n + 1 : ℝ)) (by norm_num : (0 : ℝ) ≤ 3))
          nlinarith [hmul]
        _ = (3 : ℝ) ^ (n + 1) * ((n + 1).factorial : ℝ) := by
          rw [pow_succ, Nat.factorial_succ]
          push_cast
          ring

private theorem lpNorm_integral_pow_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} {q : ℕ}
    (hq : 0 < q) (hX : MemLp X (q : ℝ≥0∞) μ) {B : ℝ}
    (hB : 0 ≤ B) (hcap : lpNorm X (q : ℝ≥0∞) μ ≤ B) :
    ∫ ω, |X ω| ^ q ∂μ ≤ B ^ q := by
  have hEq := lpNorm_eq_integral_norm_rpow_toReal
    (p := (q : ℝ≥0∞)) (μ := μ) (f := X) (by simp [hq.ne']) (by simp)
    hX.aestronglyMeasurable
  have hEq' : lpNorm X (q : ℝ≥0∞) μ =
      (∫ ω, |X ω| ^ q ∂μ) ^ ((q : ℝ)⁻¹) := by
    simpa [hEq, ENNReal.toReal_natCast, Real.norm_eq_abs, Real.rpow_natCast]
  rw [hEq'] at hcap
  have hI : 0 ≤ ∫ ω, |X ω| ^ q ∂μ := integral_nonneg fun ω => by positivity
  calc
    ∫ ω, |X ω| ^ q ∂μ =
        ((∫ ω, |X ω| ^ q ∂μ) ^ ((q : ℝ)⁻¹)) ^ (q : ℝ) := by
          rw [Real.rpow_inv_rpow hI (by exact_mod_cast hq.ne')]
    _ ≤ B ^ q := by
      calc
        _ ≤ B ^ (q : ℝ) := Real.rpow_le_rpow
          (by positivity) hcap (by positivity)
        _ = B ^ q := by rw [Real.rpow_natCast]

private theorem integrable_finsetProd_of_iIndepFun
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} (hInd : ProbabilityTheory.iIndepFun X μ)
    (hXm : ∀ i, Measurable (X i)) (hXi : ∀ i, Integrable (X i) μ)
    (s : Finset ι) : Integrable (fun ω => ∏ i ∈ s, X i ω) μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      change Integrable (fun _ : Ω => (1 : ℝ)) μ
      exact integrable_const _
  | @insert i s hi ih =>
      have hprod : (fun ω => ∏ j ∈ insert i s, X j ω) =
          fun ω => X i ω * ∏ j ∈ s, X j ω := by
        funext ω
        simp [Finset.prod_insert, hi, mul_comm]
      rw [hprod]
      have hind0 : IndepFun (X i) (∏ j ∈ s, X j) μ :=
        (hInd.indepFun_finsetProd_of_notMem hXm hi).symm
      have hind : IndepFun (X i) (fun ω => ∏ j ∈ s, X j ω) μ := by
        convert hind0 using 1
        exact (Finset.prod_fn s X).symm
      exact hind.integrable_mul (hXi i) ih

private theorem abs_pow_factorial_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} {q : ℕ}
    (hq : 0 < q) (hX : MemLp X (q : ℝ≥0∞) μ) {B : ℝ}
    (hB : 0 ≤ B) (hcap : lpNorm X (q : ℝ≥0∞) μ ≤ B * q) :
    ∫ ω, |X ω| ^ q ∂μ ≤ (3 * B) ^ q * q.factorial := by
  have hraw := lpNorm_integral_pow_le hq hX (mul_nonneg hB (by positivity)) hcap
  have hq3 := nat_pow_le_three_pow_mul_factorial q
  have hBpow : 0 ≤ B ^ q := by positivity
  have hq3' : ((q : ℝ) ^ q) ≤ (3 : ℝ) ^ q * q.factorial := by exact_mod_cast hq3
  calc
    ∫ ω, |X ω| ^ q ∂μ ≤ (B * q) ^ q := hraw
    _ = B ^ q * (q : ℝ) ^ q := by rw [mul_pow]
    _ ≤ B ^ q * ((3 : ℝ) ^ q * q.factorial) :=
      mul_le_mul_of_nonneg_left hq3' hBpow
    _ = (3 * B) ^ q * q.factorial := by rw [mul_pow]; ring

private noncomputable def evenCountHalf {ι : Type*} [Fintype ι] [DecidableEq ι]
    {s : ℕ} (k : {f : ι → ℕ // f ∈ Finset.univ.piAntidiag (2 * s) ∧
      ∀ i, Even (f i)}) : Sym ι s := by
  let f : ι →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => k.1 i / 2)
  have hsum : (∑ i, k.1 i) = 2 * s := by
    exact (Finset.mem_piAntidiag.mp k.2.1).1
  have hdouble (i : ι) : k.1 i = 2 * (k.1 i / 2) := by
    obtain ⟨n, hn⟩ := k.2.2 i
    omega
  have hhalfsum : (∑ i, k.1 i / 2) = s := by
    have hsum' : 2 * (∑ i, k.1 i / 2) = 2 * s := by
      calc
        2 * (∑ i, k.1 i / 2) = ∑ i, 2 * (k.1 i / 2) := by rw [Finset.mul_sum]
        _ = ∑ i, k.1 i := by
          apply Finset.sum_congr rfl
          intro i _
          exact (hdouble i).symm
        _ = 2 * s := hsum
    omega
  have hf : f.sum (fun _ n => n) = s := by
    rw [Finsupp.sum_fintype f (fun _ n => n) (by intro; rfl)]
    exact hhalfsum
  exact ⟨Finsupp.toMultiset f, by
    rw [Finsupp.card_toMultiset]
    exact hf⟩

private theorem evenCountHalf_injective {ι : Type*} [Fintype ι] [DecidableEq ι]
    {s : ℕ} : Function.Injective (@evenCountHalf ι _ _ s) := by
  intro x y hxy
  apply Subtype.ext
  funext i
  have hhalf : x.1 i / 2 = y.1 i / 2 := by
    have h := congrArg (fun z : Sym ι s => z.val.toFinsupp i) hxy
    simpa [evenCountHalf] using h
  obtain ⟨a, ha⟩ := x.2.2 i
  obtain ⟨b, hb⟩ := y.2.2 i
  omega

private theorem evenPiAntidiag_card_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ℕ) [Fintype {k : ι → ℕ // k ∈ Finset.univ.piAntidiag (2 * s) ∧
      ∀ i, Even (k i)}] :
    Fintype.card {k : ι → ℕ // k ∈ Finset.univ.piAntidiag (2 * s) ∧
      ∀ i, Even (k i)} ≤ (Fintype.card ι + s - 1).choose s := by
  classical
  let E := {k : ι → ℕ // k ∈ Finset.univ.piAntidiag (2 * s) ∧ ∀ i, Even (k i)}
  letI : Fintype {k : ι → ℕ // k ∈ Finset.univ.piAntidiag (2 * s)} :=
    Fintype.ofFinset (Finset.univ.piAntidiag (2 * s)) (by intro; simp)
  letI : Finite E := Finite.of_injective
    (fun k : E => (⟨k.1, k.2.1⟩ : {k : ι → ℕ // k ∈ Finset.univ.piAntidiag (2 * s)}))
    (by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun z : {k : ι → ℕ // k ∈ Finset.univ.piAntidiag (2 * s)} => z.1) h)
  have hcard1 : Fintype.card E ≤ Fintype.card (Sym ι s) :=
    Fintype.card_le_of_injective (fun k : E => evenCountHalf k) evenCountHalf_injective
  calc
    Fintype.card E ≤ Fintype.card (Sym ι s) := hcard1
    _ = (Fintype.card ι + s - 1).choose s := Sym.card_sym_eq_choose (α := ι) s

private theorem pow_eq_abs_pow_of_even {x : ℝ} {q : ℕ} (hq : Even q) :
    x ^ q = |x| ^ q := by
  calc
    x ^ q = |x ^ q| := (abs_of_nonneg (hq.pow_nonneg x)).symm
    _ = |x| ^ q := abs_pow x q

private theorem integral_pow_eq_zero_of_symmetric
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ} {q : ℕ}
    (hSymm : IdentDistrib X (fun ω => -X ω) μ μ)
    (hodd : ¬ Even q) : ∫ ω, X ω ^ q ∂μ = 0 := by
  have hpow := hSymm.comp (measurable_id.pow_const q)
  have hEq := hpow.integral_eq
  obtain ⟨r, hr⟩ := (Nat.not_even_iff_odd).mp hodd
  subst q
  have hneg : ∀ x : ℝ, (-x) ^ (2 * r + 1) = -(x ^ (2 * r + 1)) := by
    intro x
    calc
      (-x) ^ (2 * r + 1) = (-x) ^ (2 * r) * (-x) := by rw [pow_succ]
      _ = x ^ (2 * r) * (-x) := by
        congr 1
        rw [pow_mul, ← pow_mul]
        simp
      _ = -(x ^ (2 * r) * x) := by ring
      _ = -(x ^ (2 * r + 1)) := by rw [pow_succ]
  have hEq0 :
      (∫ ω, X ω ^ (2 * r + 1) ∂μ) =
        ∫ ω, (-X ω) ^ (2 * r + 1) ∂μ := by
    simpa only [Function.comp_apply, id_eq] using hEq
  have hEq' : (∫ ω, X ω ^ (2 * r + 1) ∂μ) =
      -(∫ ω, X ω ^ (2 * r + 1) ∂μ) := by
    calc
      _ = ∫ ω, (-X ω) ^ (2 * r + 1) ∂μ := hEq0
      _ = ∫ ω, -(X ω ^ (2 * r + 1)) ∂μ := by
        congr 1
        funext ω
        exact hneg (X ω)
      _ = _ := by rw [integral_neg]
  linarith

private theorem lpNorm_comp_fst_eq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} {q : ℝ≥0∞} (hX : MemLp X q μ) :
    lpNorm (fun ω : Ω × Ω => X ω.1) q (μ.prod μ) = lpNorm X q μ := by
  have h := eLpNorm_comp_measurePreserving
    (p := q) (g := X) hX.aestronglyMeasurable
    (measurePreserving_fst (μ := μ) (ν := μ))
  simpa [lpNorm, Function.comp_def] using congrArg ENNReal.toReal h

private theorem lpNorm_comp_snd_eq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} {q : ℝ≥0∞} (hX : MemLp X q μ) :
    lpNorm (fun ω : Ω × Ω => X ω.2) q (μ.prod μ) = lpNorm X q μ := by
  have h := eLpNorm_comp_measurePreserving
    (p := q) (g := X) hX.aestronglyMeasurable
    (measurePreserving_snd (μ := μ) (ν := μ))
  simpa [lpNorm, Function.comp_def] using congrArg ENNReal.toReal h

private theorem integrable_pow_of_memLp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ] {X : Ω → ℝ}
    {q : ℕ} (hX : MemLp X (q : ℝ≥0∞) μ) (hXm : Measurable X) :
    Integrable (fun ω => X ω ^ q) μ := by
  apply (integrable_norm_iff ((hXm.pow_const q).aestronglyMeasurable)).mp
  simpa [Real.norm_eq_abs, abs_pow] using hX.integrable_norm_pow'

private theorem integral_prod_pow_of_iIndep
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : ι → Ω → ℝ} {p : ℕ}
    (hInd : iIndepFun Z μ) (hZm : ∀ i, Measurable (Z i))
    (hZp : ∀ i, MemLp (Z i) (p : ℝ≥0∞) μ)
    (k : ι → ℕ) (hk : ∑ i, k i = p) :
    ∫ ω, ∏ i, Z i ω ^ k i ∂μ = ∏ i, ∫ ω, Z i ω ^ k i ∂μ := by
  classical
  let V : ι → Ω → ℝ := fun i => (fun x : ℝ => x ^ k i) ∘ Z i
  have hVk (i : ι) : k i ≤ p := by
    rw [← hk]
    exact Finset.single_le_sum (fun j hj => Nat.zero_le _) (Finset.mem_univ i)
  have hVInd : iIndepFun V μ := by
    simpa [V] using
      hInd.comp (fun i x => x ^ k i) (fun i => measurable_id.pow_const _)
  have hVMeas : ∀ i, Measurable (V i) := by
    intro i
    exact (measurable_id.pow_const _).comp (hZm i)
  have hVInt : ∀ i, Integrable (V i) μ := by
    intro i
    have hq : MemLp (Z i) ((k i : ℕ) : ℝ≥0∞) μ :=
      (hZp i).mono_exponent (by exact_mod_cast hVk i)
    change Integrable (fun ω => Z i ω ^ k i) μ
    exact integrable_pow_of_memLp hq (hZm i)
  have hprod := hVInd.integral_fun_prod_eq_prod_integral
    (fun i => (hVMeas i).aestronglyMeasurable)
  have hprod' : ∫ ω, ∏ i, V i ω ∂μ = ∏ i, ∫ ω, V i ω ∂μ := by
    simpa using hprod
  simpa [V, Function.comp_apply] using hprod'

private theorem symmetric_iIndep_sum_even_moment_le
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : ι → Ω → ℝ} {p : ℕ}
    (hpEven : Even p) (hpPos : 0 < p)
    (hInd : iIndepFun Z μ) (hZm : ∀ i, Measurable (Z i))
    (hSymm : ∀ i, IdentDistrib (Z i) (fun ω => -Z i ω) μ μ)
    (hZp : ∀ i, MemLp (Z i) (p : ℝ≥0∞) μ)
    {B : ℝ} (hB : 0 ≤ B)
    (hCap : ∀ i q, q ≤ p → Even q → 0 < q →
      lpNorm (Z i) (q : ℝ≥0∞) μ ≤ B * q) :
    ∫ ω, |∑ i, Z i ω| ^ p ∂μ ≤
      (p.factorial : ℝ) * (3 * B) ^ p *
        ((Fintype.card ι + p / 2 - 1).choose (p / 2) : ℝ) := by
  classical
  let s : Finset ι := Finset.univ
  have hMoment (i : ι) (q : ℕ) (hqp : q ≤ p) (hqEven : Even q) :
      ∫ ω, |Z i ω| ^ q ∂μ ≤ (3 * B) ^ q * q.factorial := by
    by_cases hq : q = 0
    · subst q
      simp
    have hqPos : 0 < q := Nat.pos_of_ne_zero hq
    have hqENN : (q : ℝ≥0∞) ≤ (p : ℝ≥0∞) := by exact_mod_cast hqp
    have hZq := (hZp i).mono_exponent hqENN
    have hraw := abs_pow_factorial_bound hqPos hZq hB (hCap i q hqp hqEven hqPos)
    exact hraw
  have hterm (k : ι → ℕ) (hk : k ∈ s.piAntidiag p) :
      (Nat.multinomial s k : ℝ) *
          ∫ ω, ∏ i ∈ s, Z i ω ^ k i ∂μ ≤
        if ∀ i ∈ s, Even (k i) then
          (p.factorial : ℝ) * (3 * B) ^ p else 0 := by
    have hsum : ∑ i ∈ s, k i = p := (Finset.mem_piAntidiag.mp hk).1
    have hfac := integral_prod_pow_of_iIndep hInd hZm hZp k hsum
    rw [hfac]
    by_cases he : ∀ i ∈ s, Even (k i)
    · have hprodNonneg : 0 ≤ ∏ i ∈ s, ∫ ω, Z i ω ^ k i ∂μ := by
        apply Finset.prod_nonneg
        intro i hi
        rw [← integral_congr_ae (Filter.Eventually.of_forall fun ω =>
          (pow_eq_abs_pow_of_even (he i hi)).symm)]
        exact integral_nonneg fun ω => by positivity
      have hprodMoment :
          ∏ i ∈ s, ∫ ω, Z i ω ^ k i ∂μ ≤
            ∏ i ∈ s, ((3 * B) ^ k i * (k i).factorial) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          rw [← integral_congr_ae (Filter.Eventually.of_forall fun ω =>
            (pow_eq_abs_pow_of_even (he i hi)).symm)]
          exact integral_nonneg fun ω => by positivity
        · intro i hi
          rw [← integral_congr_ae (Filter.Eventually.of_forall fun ω =>
            (pow_eq_abs_pow_of_even (he i hi)).symm)]
          have hki : k i ≤ p := by
            rw [← hsum]
            exact Finset.single_le_sum (fun j hj => Nat.zero_le _) (Finset.mem_univ i)
          exact hMoment i (k i) hki (he i hi)
      have hpow : ∏ i ∈ s, (3 * B) ^ k i = (3 * B) ^ p := by
        rw [Finset.prod_pow_eq_pow_sum, hsum]
      have hspec := Nat.multinomial_spec s k
      rw [hsum] at hspec
      have hspecR :
          (∏ i ∈ s, ((k i).factorial : ℝ)) * (Nat.multinomial s k : ℝ) =
            (p.factorial : ℝ) := by exact_mod_cast hspec
      have hcoeff :
          (Nat.multinomial s k : ℝ) *
              ∏ i ∈ s, ((3 * B) ^ k i * (k i).factorial) =
            (p.factorial : ℝ) * (3 * B) ^ p := by
        rw [Finset.prod_mul_distrib, hpow]
        calc
          (Nat.multinomial s k : ℝ) *
              ((3 * B) ^ p * (∏ i ∈ s, ((k i).factorial : ℝ))) =
            (3 * B) ^ p *
              ((∏ i ∈ s, ((k i).factorial : ℝ)) * (Nat.multinomial s k : ℝ)) := by ring
          _ = (3 * B) ^ p * (p.factorial : ℝ) := by rw [hspecR]
          _ = (p.factorial : ℝ) * (3 * B) ^ p := by ring
      rw [if_pos he]
      calc
        (Nat.multinomial s k : ℝ) *
            ∏ i ∈ s, ∫ ω, Z i ω ^ k i ∂μ
          ≤ (Nat.multinomial s k : ℝ) *
              ∏ i ∈ s, ((3 * B) ^ k i * (k i).factorial) :=
                mul_le_mul_of_nonneg_left hprodMoment (Nat.cast_nonneg _)
        _ = _ := hcoeff
    · have hi : ∃ i ∈ s, ¬ Even (k i) := by
        by_contra hn
        push Not at hn
        exact he hn
      obtain ⟨i, hi, hodd⟩ := hi
      have hzero := integral_pow_eq_zero_of_symmetric (hSymm i) hodd
      have hprodZero : ∏ j ∈ s, ∫ ω, Z j ω ^ k j ∂μ = 0 := by
        rw [Finset.prod_eq_zero (Finset.mem_univ i)]
        exact hzero
      rw [if_neg he]
      have hprodZero' : ∏ j, ∫ ω, Z j ω ^ k j ∂μ = 0 := by simpa [s] using hprodZero
      simp [hprodZero']
  have hsymmInt : Integrable (fun ω => |∑ i ∈ s, Z i ω| ^ p) μ := by
    have hsum : MemLp (fun ω => ∑ i ∈ s, Z i ω) (p : ℝ≥0∞) μ :=
      memLp_finsetSum s (fun i hi => hZp i)
    simpa [Real.norm_eq_abs, abs_pow] using hsum.integrable_norm_pow'
  have hpoint (ω : Ω) :
      (∑ i ∈ s, Z i ω) ^ p =
        ∑ k ∈ s.piAntidiag p,
          (Nat.multinomial s k : ℝ) * ∏ i ∈ s, Z i ω ^ k i := by
    exact Finset.sum_pow_eq_sum_piAntidiag s (fun i => Z i ω) p
  have hpowerNonneg (ω : Ω) : 0 ≤ (∑ i ∈ s, Z i ω) ^ p :=
    hpEven.pow_nonneg _
  have hExpand :
      ∫ ω, |∑ i ∈ s, Z i ω| ^ p ∂μ =
        ∑ k ∈ s.piAntidiag p,
          (Nat.multinomial s k : ℝ) *
            ∫ ω, ∏ i ∈ s, Z i ω ^ k i ∂μ := by
    have hsumPowInt : Integrable (fun ω => (∑ i ∈ s, Z i ω) ^ p) μ := by
      have hEq : (fun ω => |∑ i ∈ s, Z i ω| ^ p) =
          fun ω => (∑ i ∈ s, Z i ω) ^ p := by
        funext ω
        exact (pow_eq_abs_pow_of_even hpEven).symm
      exact (integrable_congr
        (Filter.Eventually.of_forall fun ω => congrFun hEq ω)).mp hsymmInt
    calc
      _ = ∫ ω, (∑ i ∈ s, Z i ω) ^ p ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun ω =>
          (pow_eq_abs_pow_of_even hpEven).symm
      _ = ∫ ω, ∑ k ∈ s.piAntidiag p,
            (Nat.multinomial s k : ℝ) * ∏ i ∈ s, Z i ω ^ k i ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hpoint
      _ = _ := by
        rw [integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro k hk
          rw [integral_const_mul]
        · intro k hk
          exact (integrable_finsetProd_of_iIndepFun
            (hInd.comp (fun i x => x ^ k i) (fun i => measurable_id.pow_const _))
            (fun i => (hZm i).pow_const _)
            (fun i => integrable_pow_of_memLp
              ((hZp i).mono_exponent (by
                have hki : k i ≤ p := by
                  rw [← (Finset.mem_piAntidiag.mp hk).1]
                  exact Finset.single_le_sum (fun j hj => Nat.zero_le _) (Finset.mem_univ i)
                exact_mod_cast hki))
              (hZm i)) s).const_mul _
  have hcount :
      (∑ k ∈ s.piAntidiag p,
        if ∀ i ∈ s, Even (k i) then (1 : ℝ) else 0) ≤
        ((Fintype.card ι + p / 2 - 1).choose (p / 2) : ℝ) := by
    rw [Finset.sum_boole]
    have hp2 : p = 2 * (p / 2) := by
      obtain ⟨r, hr⟩ := hpEven
      omega
    let t : Finset (ι → ℕ) :=
      (Finset.univ : Finset ι).piAntidiag (2 * (p / 2))
    let tEven := t.filter (fun k : ι → ℕ => ∀ i, Even (k i))
    have hE : ∀ k : ι → ℕ, k ∈ tEven ↔
        k ∈ (Finset.univ : Finset ι).piAntidiag (2 * (p / 2)) ∧
          ∀ i, Even (k i) := by
      intro k
      simp [tEven, t]
    letI : Fintype {k : ι → ℕ //
        k ∈ (Finset.univ : Finset ι).piAntidiag (2 * (p / 2)) ∧
          ∀ i, Even (k i)} := Fintype.ofFinset tEven hE
    have hcard := evenPiAntidiag_card_le (ι := ι) (p / 2)
    have hcardE : Fintype.card {k : ι → ℕ //
        k ∈ (Finset.univ : Finset ι).piAntidiag (2 * (p / 2)) ∧
          ∀ i, Even (k i)} = tEven.card :=
      Fintype.card_ofFinset tEven hE
    have hbound : (tEven.card : ℝ) ≤
        ((Fintype.card ι + p / 2 - 1).choose (p / 2) : ℝ) := by
      exact_mod_cast hcardE ▸ hcard
    have hpi : s.piAntidiag p = t := by
      dsimp [s, t]
      congr 1
    have hfilter :
        (s.piAntidiag p).filter (fun k : ι → ℕ => ∀ i ∈ s, Even (k i)) = tEven := by
      rw [hpi]
      ext k
      simp [s, tEven]
    rw [hfilter]
    exact hbound
  have hsumBound :
      ∑ k ∈ s.piAntidiag p,
          (Nat.multinomial s k : ℝ) *
            ∫ ω, ∏ i ∈ s, Z i ω ^ k i ∂μ ≤
        (p.factorial : ℝ) * (3 * B) ^ p *
          ((Fintype.card ι + p / 2 - 1).choose (p / 2) : ℝ) := by
    calc
      _ ≤ ∑ k ∈ s.piAntidiag p,
          if ∀ i ∈ s, Even (k i) then
            (p.factorial : ℝ) * (3 * B) ^ p else 0 :=
        Finset.sum_le_sum fun k hk => hterm k hk
      _ = (p.factorial : ℝ) * (3 * B) ^ p *
          (∑ k ∈ s.piAntidiag p,
            if ∀ i ∈ s, Even (k i) then (1 : ℝ) else 0) := by
        rw [mul_comm, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        split_ifs <;> simp
      _ ≤ _ := by
        exact mul_le_mul_of_nonneg_left hcount (by positivity)
  simpa [s] using hExpand.trans_le hsumBound

private theorem even_choose_le_three_mul_card_div_half
    {M p : ℕ} (hpEven : Even p) (hpPos : 0 < p) :
    ((M + p / 2 - 1).choose (p / 2) : ℝ) ≤
      (3 * ((M + p / 2 : ℕ) : ℝ) / (p / 2 : ℝ)) ^ (p / 2) := by
  let s : ℕ := p / 2
  let n : ℕ := M + s - 1
  have hpHalf : p = 2 * (p / 2) := by
    obtain ⟨r, hr⟩ := hpEven
    omega
  have hs : 0 < s := by dsimp [s]; omega
  have hsR : 0 < (s : ℝ) := by exact_mod_cast hs
  have hpHalfCast : ((p / 2 : ℕ) : ℝ) = (p : ℝ) / 2 := by
    have hcast : (p : ℝ) = 2 * (p / 2 : ℕ) := by exact_mod_cast hpHalf
    nlinarith
  have hsmall : 0 < (s : ℝ) / 3 := by positivity
  have hfac := nat_pow_le_three_pow_mul_factorial s
  have hfacR : (s : ℝ) ^ s ≤ 3 ^ s * (s.factorial : ℝ) := by
    exact_mod_cast hfac
  have hsmallPow : ((s : ℝ) / 3) ^ s ≤ (s.factorial : ℝ) := by
    rw [div_pow]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 3 ^ s)).2
    simpa [mul_comm] using hfacR
  have hrecip : 1 / (s.factorial : ℝ) ≤ 1 / ((s : ℝ) / 3) ^ s :=
    one_div_le_one_div_of_le (by positivity) hsmallPow
  have hn : ((n : ℕ) : ℝ) ≤ (M + s : ℝ) := by
    have hn' : n ≤ M + s := by dsimp [n]; omega
    exact_mod_cast hn'
  have hnum : (n : ℝ) ^ s ≤ (M + s : ℝ) ^ s := by
    exact pow_le_pow_left₀ (by positivity) hn s
  have hchoose : ((n.choose s : ℕ) : ℝ) ≤
      (n : ℝ) ^ s / (s.factorial : ℝ) := Nat.choose_le_pow_div s n
  calc
    ((M + p / 2 - 1).choose (p / 2) : ℝ) = (n.choose s : ℝ) := by
      simp [n, s]
    _ ≤ (n : ℝ) ^ s / (s.factorial : ℝ) := hchoose
    _ = (n : ℝ) ^ s * (1 / (s.factorial : ℝ)) := by ring
    _ ≤ (M + s : ℝ) ^ s * (1 / ((s : ℝ) / 3) ^ s) := by
      exact mul_le_mul hnum hrecip (by positivity) (by positivity)
    _ = (3 * (M + s : ℝ) / (s : ℝ)) ^ s := by
      calc
        _ = (M + s : ℝ) ^ s * ((3 : ℝ) ^ s / (s : ℝ) ^ s) := by
          rw [div_pow]
          field_simp [hsR.ne']
        _ = (3 * (M + s : ℝ) / (s : ℝ)) ^ s := by
          rw [div_pow, mul_pow]
          ring
    _ = (3 * ((M + p / 2 : ℕ) : ℝ) / (p / 2 : ℝ)) ^ (p / 2) := by
      simp [s, hpHalfCast]

private theorem even_factorial_choose_le
    {M p : ℕ} (hpEven : Even p) (hpPos : 0 < p) :
    (p.factorial : ℝ) * ((M + p / 2 - 1).choose (p / 2) : ℝ) ≤
      (3 * Real.sqrt ((p : ℝ) * M) + 2 * p) ^ p := by
  let s : ℕ := p / 2
  let A : ℝ := 3 * ((M + s : ℕ) : ℝ) / (s : ℝ)
  have hpHalf : p = 2 * s := by
    obtain ⟨r, hr⟩ := hpEven
    dsimp [s]
    omega
  have hs : 0 < s := by dsimp [s]; omega
  have hsR : 0 < (s : ℝ) := by exact_mod_cast hs
  have hpHalfR : (p : ℝ) = 2 * (s : ℝ) := by exact_mod_cast hpHalf
  have hA : 0 ≤ A := by positivity
  have hAalg : (p : ℝ) ^ 2 * A = 6 * (p : ℝ) * M + 3 * (p : ℝ) ^ 2 := by
    dsimp [A]
    rw [hpHalfR]
    field_simp [hsR.ne']
    push_cast
    ring
  have hrootSq : ((p : ℝ) * Real.sqrt A) ^ 2 =
      6 * (p : ℝ) * M + 3 * (p : ℝ) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hA]
    exact hAalg
  have hroot : (p : ℝ) * Real.sqrt A ≤
      3 * Real.sqrt ((p : ℝ) * M) + 2 * p := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [hrootSq]
    have hPM : Real.sqrt ((p : ℝ) * M) ^ 2 = (p : ℝ) * M :=
      Real.sq_sqrt (by positivity)
    have hpM : 0 ≤ (p : ℝ) * M := by positivity
    have hcross : 0 ≤ 12 * (p : ℝ) * Real.sqrt ((p : ℝ) * M) := by positivity
    nlinarith [hPM, hpM, hcross, sq_nonneg (p : ℝ)]
  have hchoose := even_choose_le_three_mul_card_div_half (M := M) hpEven hpPos
  have hpHalfNat : p / 2 = s := by dsimp [s]
  have hnum : ((M + p / 2 : ℕ) : ℝ) = ((M + s : ℕ) : ℝ) := by
    rw [hpHalfNat]
  have hden : (p : ℝ) / 2 = (s : ℝ) := by
    rw [hpHalfR]
    norm_num
  have hchooseA : ((M + p / 2 - 1).choose (p / 2) : ℝ) ≤ A ^ (p / 2) := by
    calc
      _ ≤ (3 * ((M + p / 2 : ℕ) : ℝ) / ((p : ℝ) / 2)) ^ (p / 2) := hchoose
      _ = A ^ (p / 2) := by
        dsimp [A]
        rw [← hnum, ← hden]
  have hfac : (p.factorial : ℝ) ≤ (p : ℝ) ^ p := by
    exact_mod_cast Nat.factorial_le_pow p
  have hbound : (p.factorial : ℝ) *
      ((M + p / 2 - 1).choose (p / 2) : ℝ) ≤
      (p : ℝ) ^ p * A ^ (p / 2) :=
    mul_le_mul hfac hchooseA (by positivity) (by positivity)
  have hsqrtPow : (Real.sqrt A) ^ p = A ^ (p / 2) := by
    calc
      (Real.sqrt A) ^ p = (Real.sqrt A) ^ (2 * s) := by rw [hpHalf]
      _ = ((Real.sqrt A) ^ 2) ^ s := by rw [pow_mul]
      _ = A ^ s := by rw [Real.sq_sqrt hA]
      _ = A ^ (p / 2) := by rw [show p / 2 = s by rfl]
  have hpow : (p : ℝ) ^ p * A ^ (p / 2) =
      ((p : ℝ) * Real.sqrt A) ^ p := by
    rw [mul_pow, hsqrtPow]
  calc
    _ ≤ (p : ℝ) ^ p * A ^ (p / 2) := hbound
    _ = ((p : ℝ) * Real.sqrt A) ^ p := hpow
    _ ≤ (3 * Real.sqrt ((p : ℝ) * M) + 2 * p) ^ p := by
      exact pow_le_pow_left₀ (by positivity) hroot p

private theorem lpNorm_le_of_integral_abs_pow_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {q : ℕ} (hq : 0 < q) (hX : MemLp X (q : ℝ≥0∞) μ)
    {R : ℝ} (hR : 0 ≤ R)
    (hI : ∫ ω, |X ω| ^ q ∂μ ≤ R ^ q) :
    lpNorm X (q : ℝ≥0∞) μ ≤ R := by
  have hEq := lpNorm_eq_integral_norm_rpow_toReal
    (p := (q : ℝ≥0∞)) (μ := μ) (f := X) (by simp [hq.ne']) (by simp)
    hX.aestronglyMeasurable
  have hEq' : lpNorm X (q : ℝ≥0∞) μ =
      (∫ ω, |X ω| ^ q ∂μ) ^ ((q : ℝ)⁻¹) := by
    simpa [hEq, ENNReal.toReal_natCast, Real.norm_eq_abs, Real.rpow_natCast]
  have hI0 : 0 ≤ ∫ ω, |X ω| ^ q ∂μ :=
    integral_nonneg fun ω => by positivity
  have hrootR : (R ^ q) ^ ((q : ℝ)⁻¹) = R := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR,
      mul_inv_cancel₀ (by exact_mod_cast hq.ne'), Real.rpow_one]
  rw [hEq']
  calc
    (∫ ω, |X ω| ^ q ∂μ) ^ ((q : ℝ)⁻¹) ≤
        (R ^ q) ^ ((q : ℝ)⁻¹) :=
      Real.rpow_le_rpow hI0 hI (by positivity)
    _ = R := hrootR

theorem finite_even_centered_independent_sum_lpNorm_le
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [Fintype ι] [DecidableEq ι] {X : ι → Ω → ℝ} {p : ℕ}
    (hpEven : Even p) (hpMin : 12 ≤ p)
    (hInd : iIndepFun X μ) (hXm : ∀ i, Measurable (X i))
    (hX : ∀ i, MemLp (X i) (p : ℝ≥0∞) μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hCap : ∀ i q, 12 ≤ q → q ≤ p → Even q →
      lpNorm (X i) (q : ℝ≥0∞) μ ≤ C * q) :
    lpNorm (fun ω => ∑ i, (X i ω - μ[X i])) (p : ℝ≥0∞) μ ≤
        108 * C * (Real.sqrt ((p : ℝ) * Fintype.card ι) + p) := by
  classical
  have hpPos : 0 < p := by omega
  let Z : ι → Ω × Ω → ℝ := fun i ω => X i ω.1 - X i ω.2
  have hZInd : iIndepFun Z (μ.prod μ) :=
    Homogenization.IndependentSums.iIndepFun_sub_comp_fst_comp_snd_prod hInd hXm
  have hZMeas : ∀ i, Measurable (Z i) := by
    intro i
    exact (hXm i).comp measurable_fst |>.sub ((hXm i).comp measurable_snd)
  have hZSymm : ∀ i, IdentDistrib (Z i) (fun ω => -Z i ω) (μ.prod μ) (μ.prod μ) := by
    intro i
    exact Homogenization.IndependentSums.identDistrib_sub_comp_fst_comp_snd_prod_neg
      (hXm i)
  have hZp : ∀ i, MemLp (Z i) (p : ℝ≥0∞) (μ.prod μ) := by
    intro i
    change MemLp (fun ω : Ω × Ω => X i ω.1 - X i ω.2) (p : ℝ≥0∞) (μ.prod μ)
    exact ((hX i).comp_fst μ).sub ((hX i).comp_snd μ)
  have hRawCap : ∀ i q, q ≤ p → Even q → 0 < q →
      lpNorm (X i) (q : ℝ≥0∞) μ ≤ 6 * C * q := by
    intro i q hqp hqEven hqPos
    by_cases hq12 : 12 ≤ q
    · calc
        lpNorm (X i) (q : ℝ≥0∞) μ ≤ C * q := hCap i q hq12 hqp hqEven
        _ ≤ 6 * C * q := by
          have hnonneg : 0 ≤ C * q := mul_nonneg hC (by positivity)
          nlinarith
    · have hqle12 : q ≤ 12 := by omega
      have hX12 : MemLp (X i) 12 μ :=
        (hX i).mono_exponent (by exact_mod_cast hpMin)
      have hmonoE : eLpNorm (X i) (q : ℝ≥0∞) μ ≤ eLpNorm (X i) 12 μ :=
        eLpNorm_le_eLpNorm_of_exponent_le (by exact_mod_cast hqle12)
      have hmono : lpNorm (X i) (q : ℝ≥0∞) μ ≤ lpNorm (X i) 12 μ := by
        change (eLpNorm (X i) (q : ℝ≥0∞) μ).toReal ≤
          (eLpNorm (X i) 12 μ).toReal
        exact ENNReal.toReal_mono hX12.eLpNorm_ne_top hmonoE
      have hcap12 : lpNorm (X i) 12 μ ≤ C * 12 :=
        hCap i 12 (by norm_num) hpMin ⟨6, by norm_num⟩
      have hqge2 : 2 ≤ q := by
        obtain ⟨r, hr⟩ := hqEven
        omega
      calc
        lpNorm (X i) (q : ℝ≥0∞) μ ≤ lpNorm (X i) 12 μ := hmono
        _ ≤ C * 12 := hcap12
        _ ≤ 6 * C * q := by
          have hqminus : 0 ≤ (q : ℝ) - 2 := by
            exact_mod_cast (show 0 ≤ q - 2 by omega)
          have hprod : 0 ≤ C * ((q : ℝ) - 2) := mul_nonneg hC hqminus
          nlinarith
  have hZCap : ∀ i q, q ≤ p → Even q → 0 < q →
      lpNorm (Z i) (q : ℝ≥0∞) (μ.prod μ) ≤ 12 * C * q := by
    intro i q hqp hqEven hqPos
    have hXq : MemLp (X i) (q : ℝ≥0∞) μ :=
      (hX i).mono_exponent (by exact_mod_cast hqp)
    have hqOne : (1 : ℝ≥0∞) ≤ (q : ℝ≥0∞) := by
      exact_mod_cast (show 1 ≤ q from by omega)
    calc
      lpNorm (Z i) (q : ℝ≥0∞) (μ.prod μ) =
          lpNorm (fun ω : Ω × Ω => X i ω.1 - X i ω.2) (q : ℝ≥0∞) (μ.prod μ) := rfl
      _ ≤ lpNorm (fun ω : Ω × Ω => X i ω.1) (q : ℝ≥0∞) (μ.prod μ) +
          lpNorm (fun ω : Ω × Ω => X i ω.2) (q : ℝ≥0∞) (μ.prod μ) :=
        lpNorm_sub_le (hXq.comp_fst μ) hqOne
      _ = lpNorm (X i) (q : ℝ≥0∞) μ + lpNorm (X i) (q : ℝ≥0∞) μ := by
        rw [lpNorm_comp_fst_eq hXq, lpNorm_comp_snd_eq hXq]
      _ ≤ 6 * C * q + 6 * C * q :=
        add_le_add (hRawCap i q hqp hqEven hqPos) (hRawCap i q hqp hqEven hqPos)
      _ = 12 * C * q := by ring
  have hSymMoment := symmetric_iIndep_sum_even_moment_le
    hpEven hpPos hZInd hZMeas hZSymm hZp (B := 12 * C) (by positivity) hZCap
  have h36 : 3 * (12 * C) = 36 * C := by ring
  rw [h36] at hSymMoment
  have hZsum : MemLp (fun ω : Ω × Ω => ∑ i, Z i ω) (p : ℝ≥0∞) (μ.prod μ) :=
    memLp_finsetSum Finset.univ (fun i _ => hZp i)
  have hSymInt : Integrable
      (fun ω : Ω × Ω =>
        |Homogenization.IndependentSums.symmetrizedFinsetSum X Finset.univ ω| ^ p)
      (μ.prod μ) := by
    simpa [Homogenization.IndependentSums.symmetrizedFinsetSum, Z,
      Real.norm_eq_abs, abs_pow] using hZsum.integrable_norm_pow'
  have hXint : ∀ i, Integrable (X i) μ := by
    intro i
    rw [← memLp_one_iff_integrable]
    exact (hX i).mono_exponent (by exact_mod_cast (by omega : 1 ≤ p))
  have hcenterEq :
      Homogenization.IndependentSums.centeredFinsetSum X μ Finset.univ =
        fun ω => ∑ i, (X i ω - μ[X i]) := by
    funext ω
    simp [Homogenization.IndependentSums.centeredFinsetSum]
  have hCenterMem : MemLp
      (Homogenization.IndependentSums.centeredFinsetSum X μ Finset.univ)
      (p : ℝ≥0∞) μ := by
    have hterms : ∀ i, MemLp (fun ω => X i ω - μ[X i]) (p : ℝ≥0∞) μ := by
      intro i
      exact (hX i).sub (memLp_const (μ[X i]))
    have hsum : MemLp (fun ω => ∑ i, (X i ω - μ[X i]))
        (p : ℝ≥0∞) μ :=
      memLp_finsetSum Finset.univ (fun i _ => hterms i)
    rw [hcenterEq]
    exact hsum
  have hSymmetrize :=
    Homogenization.IndependentSums.integral_abs_centeredFinsetSum_pow_le_integral_abs_symmetrizedFinsetSum_pow
      (μ := μ) (X := X) (s := Finset.univ) (p := p)
      (by omega) (by intro i hi; exact hXint i) hSymInt
  have hCenterIntegral :
      ∫ ω, |Homogenization.IndependentSums.centeredFinsetSum X μ Finset.univ ω| ^ p ∂μ ≤
        (p.factorial : ℝ) * (36 * C) ^ p *
          ((Fintype.card ι + p / 2 - 1).choose (p / 2) : ℝ) := by
    calc
      _ ≤ ∫ ω : Ω × Ω,
          |Homogenization.IndependentSums.symmetrizedFinsetSum X Finset.univ ω| ^ p
            ∂(μ.prod μ) := hSymmetrize
      _ ≤ _ := by simpa [Homogenization.IndependentSums.symmetrizedFinsetSum, Z] using hSymMoment
  let R : ℝ := 108 * C * (Real.sqrt ((p : ℝ) * Fintype.card ι) + p)
  have hR : 0 ≤ R := by positivity
  have hRootCap := even_factorial_choose_le (M := Fintype.card ι) hpEven hpPos
  have hPowBound : (p.factorial : ℝ) * (36 * C) ^ p *
      ((Fintype.card ι + p / 2 - 1).choose (p / 2) : ℝ) ≤ R ^ p := by
    have hscaled :
        (p.factorial : ℝ) * (36 * C) ^ p *
          ((Fintype.card ι + p / 2 - 1).choose (p / 2) : ℝ) ≤
        (36 * C * (3 * Real.sqrt ((p : ℝ) * Fintype.card ι) + 2 * p)) ^ p := by
      calc
        _ = (36 * C) ^ p * ((p.factorial : ℝ) *
            ((Fintype.card ι + p / 2 - 1).choose (p / 2) : ℝ)) := by ring
        _ ≤ (36 * C) ^ p *
            (3 * Real.sqrt ((p : ℝ) * Fintype.card ι) + 2 * p) ^ p :=
          mul_le_mul_of_nonneg_left hRootCap (by positivity)
        _ = _ := by rw [← mul_pow]
    have hbase : 36 * C *
        (3 * Real.sqrt ((p : ℝ) * Fintype.card ι) + 2 * p) ≤ R := by
      dsimp [R]
      have hpC : 0 ≤ C * (p : ℝ) := mul_nonneg hC (by positivity)
      nlinarith
    exact hscaled.trans (pow_le_pow_left₀ (by positivity) hbase p)
  have hLp := lpNorm_le_of_integral_abs_pow_le hpPos hCenterMem hR
    (hCenterIntegral.trans hPowBound)
  rw [← hcenterEq]
  exact hLp

end ASDExplicitGamma.AllOrder
