module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! # Interval sine and cosine Parseval identities -/

@[expose] public section

open MeasureTheory Set

namespace ASDExplicitGamma.Model

private noncomputable def bflatOddExtension (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x ∈ Icc (0 : ℝ) 1 then f x else if x ∈ Ioc 1 2 then -f (2-x) else 0

private noncomputable def bflatEvenExtension (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x ∈ Icc (0 : ℝ) 1 then f x else if x ∈ Ioc 1 2 then f (2-x) else 0

private theorem bflat_interval_finite (a b : ℝ) :
    IsFiniteMeasure (volume.restrict (Ioc a b)) := by
  refine ⟨?_⟩
  simpa only [Measure.restrict_apply_univ, Set.univ_inter] using
    (measure_Ioc_lt_top (μ := volume) (a := a) (b := b))

private theorem bflat_intervalIntegrable_of_bound {E : Type*}
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {f : ℝ → E} {C : ℝ} (hf : Measurable f) (hC : ∀ x, ‖f x‖ ≤ C)
    {a b : ℝ} (hab : a ≤ b) : IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  apply volume.integrableOn_of_bounded (s := Ioc a b)
  · exact (measure_Ioc_lt_top (μ := volume) (a := a) (b := b)).ne
  · exact hf.aestronglyMeasurable
  · filter_upwards [] with x
    exact hC x

private theorem bflat_extension_bound (f : ℝ → ℝ) (C : ℝ)
    (hC : ∀ x, |f x| ≤ C) (x : ℝ) :
    |bflatOddExtension f x| ≤ C ∧ |bflatEvenExtension f x| ≤ C := by
  constructor <;> simp only [bflatOddExtension, bflatEvenExtension]
  · split_ifs with h₁ h₂
    · exact hC x
    · simpa [abs_neg] using hC (2-x)
    · have hC' : 0 ≤ C := le_trans (abs_nonneg (f x)) (hC x)
      simpa [abs_of_nonneg hC'] using hC'
  · split_ifs with h₁ h₂
    · exact hC x
    · exact hC (2-x)
    · have hC' : 0 ≤ C := le_trans (abs_nonneg (f x)) (hC x)
      simpa [abs_of_nonneg hC'] using hC'

private theorem bflat_odd_extension_memLp {f : ℝ → ℝ} {C : ℝ}
    (hf : Measurable f) (_hC : 0 ≤ C) (hbound : ∀ x, |f x| ≤ C) :
    MemLp (fun x => (bflatOddExtension f x : ℂ)) 2 (volume.restrict (Ioc 0 2)) := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 2)
  letI : IsFiniteMeasure μ := bflat_interval_finite 0 2
  have hmeas : Measurable (fun x => (bflatOddExtension f x : ℂ)) := by
    have hext : Measurable (bflatOddExtension f) := by
      unfold bflatOddExtension
      exact Measurable.ite measurableSet_Icc hf
        (Measurable.ite measurableSet_Ioc (measurable_neg.comp
          (hf.comp (measurable_const.sub measurable_id))) measurable_const)
    exact Complex.measurable_ofReal.comp hext
  apply MemLp.of_bound hmeas.aestronglyMeasurable C
  filter_upwards [] with x
  have hb := (bflat_extension_bound f C hbound x).1
  simpa only [Complex.norm_real, Real.norm_eq_abs] using hb

private theorem bflat_even_extension_memLp {f : ℝ → ℝ} {C : ℝ}
    (hf : Measurable f) (_hC : 0 ≤ C) (hbound : ∀ x, |f x| ≤ C) :
    MemLp (fun x => (bflatEvenExtension f x : ℂ)) 2 (volume.restrict (Ioc 0 2)) := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 2)
  letI : IsFiniteMeasure μ := bflat_interval_finite 0 2
  have hmeas : Measurable (fun x => (bflatEvenExtension f x : ℂ)) := by
    have hext : Measurable (bflatEvenExtension f) := by
      unfold bflatEvenExtension
      exact Measurable.ite measurableSet_Icc hf
        (Measurable.ite measurableSet_Ioc (hf.comp (measurable_const.sub measurable_id))
          measurable_const)
    exact Complex.measurable_ofReal.comp hext
  apply MemLp.of_bound hmeas.aestronglyMeasurable C
  filter_upwards [] with x
  have hb := (bflat_extension_bound f C hbound x).2
  simpa only [Complex.norm_real, Real.norm_eq_abs] using hb

private theorem bflat_phase (m : ℕ) (x : ℝ) :
    fourier (-((m+1:ℕ):ℤ)) (x : AddCircle (2:ℝ)) =
      (Real.cos (Real.pi * ((m+1:ℕ):ℝ) * x) : ℂ) -
        Complex.I * (Real.sin (Real.pi * ((m+1:ℕ):ℝ) * x) : ℂ) := by
  haveI : Fact (0 < (2:ℝ)) := ⟨by norm_num⟩
  rw [fourier_coe_apply]
  have harg :
      (2 * (Real.pi:ℂ) * Complex.I * (↑(-((m+1:ℕ):ℤ)):ℂ) * (x:ℂ) / (2:ℂ)) =
        ((-(Real.pi * ((m+1:ℕ):ℝ) * x):ℝ):ℂ) * Complex.I := by
    push_cast
    ring
  calc
    Complex.exp _ = Complex.exp (((-(Real.pi * ((m+1:ℕ):ℝ) * x):ℝ):ℂ) * Complex.I) :=
      congrArg Complex.exp harg
    _ = _ := by
      rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
        Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
      ring

private theorem bflat_fourier_phase_shift (m : ℕ) (x : ℝ) :
    fourier (-((m+1:ℕ):ℤ)) ((2-x : ℝ) : AddCircle (2:ℝ)) =
      fourier (-((m+1:ℕ):ℤ)) ((-x : ℝ) : AddCircle (2:ℝ)) := by
  haveI : Fact (0 < (2:ℝ)) := ⟨by norm_num⟩
  have h : (2-x:ℝ) = -x + 2 := by ring
  rw [h, AddCircle.coe_add_period]

private noncomputable def bflatModePhase (m : ℕ) (x : ℝ) : ℂ :=
  fourier (-((m+1:ℕ):ℤ)) (x : AddCircle (2:ℝ))

private noncomputable def bflatExtension (f : ℝ → ℝ) (odd : Bool) (x : ℝ) : ℝ :=
  match odd with
  | true => bflatOddExtension f x
  | false => bflatEvenExtension f x

private theorem bflatExtension_weighted_integral
    {f : ℝ → ℝ} {C : ℝ} (hf : Continuous f) (hbound : ∀ x, |f x| ≤ C)
    (m : ℕ) (odd : Bool) :
    ∫ x in (0:ℝ)..2,
        bflatModePhase m x * (bflatExtension f odd x : ℂ) =
      ∫ x in (0:ℝ)..1,
        (bflatModePhase m x +
          (if odd then -bflatModePhase m (-x) else bflatModePhase m (-x))) *
            (f x : ℂ) := by
  classical
  haveI : Fact (0 < (2:ℝ)) := ⟨by norm_num⟩
  let p : ℝ → ℂ := bflatModePhase m
  let F : ℝ → ℂ := fun x => (bflatExtension f odd x : ℂ)
  have hfmeas : Measurable f := hf.measurable
  have hextMeas : Measurable (bflatExtension f odd) := by
    cases odd with
    | true =>
        change Measurable (bflatOddExtension f)
        unfold bflatOddExtension
        exact Measurable.ite measurableSet_Icc hfmeas
          (Measurable.ite measurableSet_Ioc
            (measurable_neg.comp (hfmeas.comp (measurable_const.sub measurable_id)))
            measurable_const)
    | false =>
        change Measurable (bflatEvenExtension f)
        unfold bflatEvenExtension
        exact Measurable.ite measurableSet_Icc hfmeas
          (Measurable.ite measurableSet_Ioc
            (hfmeas.comp (measurable_const.sub measurable_id)) measurable_const)
  have hFmeas : Measurable F := Complex.measurable_ofReal.comp hextMeas
  have hpcont : Continuous p := by
    exact (map_continuous (fourier (-((m+1:ℕ):ℤ)))).comp (AddCircle.continuous_mk' _)
  have hpmeas : Measurable p := hpcont.measurable
  have hpNorm (x : ℝ) : ‖p x‖ = 1 := by
    change ‖fourier (-((m+1:ℕ):ℤ)) (x : AddCircle (2:ℝ))‖ = 1
    rw [fourier_coe_apply, Complex.norm_exp]
    simp
  have hFbound (x : ℝ) : ‖F x‖ ≤ C := by
    have hb := bflat_extension_bound f C hbound x
    by_cases ho : odd
    · simpa [F, bflatExtension, ho, Complex.norm_real, Real.norm_eq_abs] using hb.1
    · simpa [F, bflatExtension, ho, Complex.norm_real, Real.norm_eq_abs] using hb.2
  have hprodMeas : Measurable (fun x => p x * F x) := hpmeas.mul hFmeas
  have hprodInt {a b : ℝ} (hab : a ≤ b) :
      IntervalIntegrable (fun x => p x * F x) volume a b :=
    bflat_intervalIntegrable_of_bound hprodMeas
      (fun x => by rw [norm_mul, hpNorm, one_mul]; exact hFbound x) hab
  have hleft : (∫ x in (0:ℝ)..1, p x * F x) =
      ∫ x in (0:ℝ)..1, p x * (f x : ℂ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Icc (0:ℝ) 1 := by simpa using hx
    change p x * ((bflatExtension f odd x : ℝ) : ℂ) = p x * (f x : ℂ)
    cases odd with
    | false => simp only [bflatExtension, bflatEvenExtension, if_pos hx']
    | true => simp only [bflatExtension, bflatOddExtension, if_pos hx']
  have hright : (∫ x in (1:ℝ)..2, p x * F x) =
      ∫ x in (1:ℝ)..2,
        p x * (((if odd then -1 else 1 : ℝ) * f (2-x) : ℝ) : ℂ) := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro x hx
    have hx' : x ∈ Ioc (1:ℝ) 2 := ⟨hx.1, hx.2.le⟩
    have hxNot : x ∉ Icc (0:ℝ) 1 := by
      intro hh
      exact (not_le_of_gt hx.1) hh.2
    change p x * ((bflatExtension f odd x : ℝ) : ℂ) =
      p x * (((if odd then -1 else 1 : ℝ) * f (2-x) : ℝ) : ℂ)
    cases odd with
    | false => simp [bflatExtension, bflatEvenExtension, hxNot, hx']
    | true => simp [bflatExtension, bflatOddExtension, hxNot, hx']
  have hreflect :
      (∫ x in (1:ℝ)..2,
          p x * (((if odd then -1 else 1 : ℝ) * f (2-x) : ℝ) : ℂ)) =
        ∫ x in (0:ℝ)..1,
          p (2-x) * (((if odd then -1 else 1 : ℝ) * f x : ℝ) : ℂ) := by
    have hcomp := intervalIntegral.integral_comp_sub_left
      (fun x : ℝ => p (2-x) * (((if odd then -1 else 1 : ℝ) * f x : ℝ) : ℂ))
      (a := (1:ℝ)) (b := 2) 2
    simpa only [sub_self, sub_zero, sub_sub_cancel,
      show (2:ℝ) - 1 = 1 by norm_num] using hcomp
  have hpShift (x : ℝ) : p (2-x) = p (-x) := by
    dsimp [p]
    exact bflat_fourier_phase_shift m x
  have hfirstInt : IntervalIntegrable (fun x => p x * (f x : ℂ)) volume 0 1 :=
    bflat_intervalIntegrable_of_bound (hpmeas.mul
      (Complex.measurable_ofReal.comp hfmeas))
      (fun x => by
        change ‖p x * (f x : ℂ)‖ ≤ C
        rw [norm_mul, hpNorm, one_mul, Complex.norm_real, Real.norm_eq_abs]
        exact hbound x) (by norm_num)
  have hsecondInt : IntervalIntegrable
      (fun x => (if odd then -p (-x) else p (-x)) * (f x : ℂ)) volume 0 1 := by
    apply bflat_intervalIntegrable_of_bound
    · have hneg : Measurable (fun x : ℝ => p (-x)) := hpmeas.comp measurable_neg
      have hreal : Measurable (fun x : ℝ => (f x : ℂ)) :=
        Complex.measurable_ofReal.comp hfmeas
      have hminus : Measurable (fun x : ℝ => -p (-x) * (f x : ℂ)) :=
        hneg.neg.mul hreal
      have hplus : Measurable (fun x : ℝ => p (-x) * (f x : ℂ)) :=
        hneg.mul hreal
      cases odd with
      | false => simpa using hplus
      | true => simpa using hminus
    · intro x
      change ‖(if odd then -p (-x) else p (-x)) * (f x : ℂ)‖ ≤ C
      have hfactor : ‖if odd then -p (-x) else p (-x)‖ = 1 := by
        by_cases ho : odd = true <;> simp [ho, norm_neg, hpNorm]
      rw [norm_mul, hfactor, one_mul, Complex.norm_real, Real.norm_eq_abs]
      exact hbound x
    · norm_num
  calc
    ∫ x in (0:ℝ)..2, p x * F x =
        (∫ x in (0:ℝ)..1, p x * F x) +
          ∫ x in (1:ℝ)..2, p x * F x :=
      (intervalIntegral.integral_add_adjacent_intervals (hprodInt (by norm_num))
        (hprodInt (by norm_num))).symm
    _ = (∫ x in (0:ℝ)..1, p x * (f x : ℂ)) +
          ∫ x in (0:ℝ)..1,
            p (2-x) * (((if odd then -1 else 1 : ℝ) * f x : ℝ) : ℂ) := by
      rw [hleft, hright, hreflect]
    _ = (∫ x in (0:ℝ)..1, p x * (f x : ℂ)) +
          ∫ x in (0:ℝ)..1,
            (if odd then -p (-x) else p (-x)) * (f x : ℂ) := by
      congr 1
      apply intervalIntegral.integral_congr
      intro x hx
      change p (2-x) * (((if odd then -1 else 1 : ℝ) * f x : ℝ) : ℂ) =
        (if odd then -p (-x) else p (-x)) * (f x : ℂ)
      rw [hpShift x]
      by_cases ho : odd = true <;> simp [ho]
      <;> ring
    _ = ∫ x in (0:ℝ)..1,
          (p x + (if odd then -p (-x) else p (-x))) * (f x : ℂ) := by
      rw [← intervalIntegral.integral_add hfirstInt hsecondInt]
      apply intervalIntegral.integral_congr
      intro x hx
      ring

private theorem bflat_phase_pair (m : ℕ) (x : ℝ) :
    (bflatModePhase m x - bflatModePhase m (-x) =
        -2 * Complex.I *
          (Real.sin (Real.pi * ((m+1:ℕ):ℝ) * x) : ℂ)) ∧
    (bflatModePhase m x + bflatModePhase m (-x) =
        2 * (Real.cos (Real.pi * ((m+1:ℕ):ℝ) * x) : ℂ)) := by
  haveI : Fact (0 < (2:ℝ)) := ⟨by norm_num⟩
  constructor
  · change fourier (-((m+1:ℕ):ℤ)) (x : AddCircle (2:ℝ)) -
        fourier (-((m+1:ℕ):ℤ)) ((-x:ℝ):AddCircle (2:ℝ)) = _
    rw [bflat_phase m x, bflat_phase m (-x)]
    have ha : Real.pi * ((m+1:ℕ):ℝ) * (-x) =
        -(Real.pi * ((m+1:ℕ):ℝ) * x) := by ring
    rw [ha, Real.cos_neg, Real.sin_neg]
    simp only [Complex.ofReal_neg]
    ring_nf
  · change fourier (-((m+1:ℕ):ℤ)) (x : AddCircle (2:ℝ)) +
        fourier (-((m+1:ℕ):ℤ)) ((-x:ℝ):AddCircle (2:ℝ)) = _
    rw [bflat_phase m x, bflat_phase m (-x)]
    have ha : Real.pi * ((m+1:ℕ):ℝ) * (-x) =
        -(Real.pi * ((m+1:ℕ):ℝ) * x) := by ring
    rw [ha, Real.cos_neg, Real.sin_neg]
    simp only [Complex.ofReal_neg]
    ring_nf

private theorem bflat_interval_conj {a b : ℝ} (hab : a < b)
    {f g : ℝ → ℂ} (hfg : ∀ x, f x = star (g x)) :
    (∫ x in a..b, f x) = star (∫ x in a..b, g x) := by
  rw [intervalIntegral.integral_of_le hab.le, intervalIntegral.integral_of_le hab.le]
  rw [← integral_indicator measurableSet_Ioc, ← integral_indicator measurableSet_Ioc]
  calc
    (∫ x, (Ioc a b).indicator f x) =
        ∫ x, star ((Ioc a b).indicator g x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : x ∈ Ioc a b <;> simp [hx, hfg]
    _ = star (∫ x, (Ioc a b).indicator g x) :=
      integral_conj

private theorem bflat_fourierCoeffOn_neg_conj {a b : ℝ} (hab : a < b)
    {f : ℝ → ℂ} (hf : ∀ x, star (f x) = f x) (n : ℤ) :
    fourierCoeffOn hab f (-n) = star (fourierCoeffOn hab f n) := by
  have hI : (∫ x in a..b, fourier n (x : AddCircle (b-a)) * f x) =
      star (∫ x in a..b, fourier (-n) (x : AddCircle (b-a)) * f x) :=
    bflat_interval_conj hab
      (f := fun x => fourier n (x : AddCircle (b-a)) * f x)
      (g := fun x => fourier (-n) (x : AddCircle (b-a)) * f x) (by
        intro x
        rw [star_mul, hf x]
        rw [show star (fourier (-n) (x : AddCircle (b-a))) =
          fourier n (x : AddCircle (b-a)) by
            rw [fourier_neg, starRingEnd_apply, star_star]]
        ring)
  rw [fourierCoeffOn_eq_integral, fourierCoeffOn_eq_integral]
  simp only [neg_neg, smul_eq_mul]
  rw [star_smul]
  simp only [star_trivial]
  rw [hI]

private theorem bflat_odd_fourierCoeffOn_pos {f : ℝ → ℝ} {C : ℝ}
    (hf : Continuous f) (hC : ∀ x, |f x| ≤ C) (m : ℕ) :
    fourierCoeffOn (show (0:ℝ) < 2 by norm_num)
        (fun x => (bflatOddExtension f x : ℂ)) ((m+1:ℕ):ℤ) =
      -Complex.I * (∫ x in (0:ℝ)..1,
        (f x : ℂ) * (Real.sin (Real.pi * ((m+1:ℕ):ℝ) * x) : ℂ)) := by
  have hweighted := bflatExtension_weighted_integral hf hC m true
  have hfold :
      (∫ x in (0:ℝ)..2, bflatModePhase m x *
        (bflatOddExtension f x : ℂ)) =
      ∫ x in (0:ℝ)..1,
        (bflatModePhase m x - bflatModePhase m (-x)) * (f x : ℂ) := by
    simpa only [bflatExtension, if_pos rfl, if_true, sub_eq_add_neg] using hweighted
  have htrig :
      (∫ x in (0:ℝ)..1,
        (bflatModePhase m x - bflatModePhase m (-x)) * (f x : ℂ)) =
      -2 * Complex.I * (∫ x in (0:ℝ)..1,
        (f x : ℂ) * (Real.sin (Real.pi * ((m+1:ℕ):ℝ) * x) : ℂ)) := by
    calc
      _ = ∫ x in (0:ℝ)..1,
          (-2 * Complex.I) * ((f x : ℂ) *
            (Real.sin (Real.pi * ((m+1:ℕ):ℝ) * x) : ℂ)) := by
        apply intervalIntegral.integral_congr
        intro x hx
        change (bflatModePhase m x - bflatModePhase m (-x)) * (f x : ℂ) = _
        rw [(bflat_phase_pair m x).1]
        ring
      _ = _ := by rw [intervalIntegral.integral_const_mul]
  calc
    _ = (1/2:ℝ) • ∫ x in (0:ℝ)..2,
          bflatModePhase m x * (bflatOddExtension f x : ℂ) := by
      rw [fourierCoeffOn_eq_integral]
      congr 1
      · norm_num
      · apply intervalIntegral.integral_congr
        intro x hx
        simp [bflatModePhase, smul_eq_mul]
    _ = (1/2:ℝ) •
          (-2 * Complex.I * (∫ x in (0:ℝ)..1,
            (f x : ℂ) * (Real.sin (Real.pi * ((m+1:ℕ):ℝ) * x) : ℂ))) := by
      rw [hfold, htrig]
    _ = _ := by norm_num [smul_eq_mul]; ring

private theorem bflat_even_fourierCoeffOn_pos {f : ℝ → ℝ} {C : ℝ}
    (hf : Continuous f) (hC : ∀ x, |f x| ≤ C) (m : ℕ) :
    fourierCoeffOn (show (0:ℝ) < 2 by norm_num)
        (fun x => (bflatEvenExtension f x : ℂ)) ((m+1:ℕ):ℤ) =
      ∫ x in (0:ℝ)..1,
        (f x : ℂ) * (Real.cos (Real.pi * ((m+1:ℕ):ℝ) * x) : ℂ) := by
  have hweighted := bflatExtension_weighted_integral hf hC m false
  have hfold :
      (∫ x in (0:ℝ)..2, bflatModePhase m x *
        (bflatEvenExtension f x : ℂ)) =
      ∫ x in (0:ℝ)..1,
        (bflatModePhase m x + bflatModePhase m (-x)) * (f x : ℂ) := by
    simpa [bflatExtension] using hweighted
  have htrig :
      (∫ x in (0:ℝ)..1,
        (bflatModePhase m x + bflatModePhase m (-x)) * (f x : ℂ)) =
      2 * (∫ x in (0:ℝ)..1,
        (f x : ℂ) * (Real.cos (Real.pi * ((m+1:ℕ):ℝ) * x) : ℂ)) := by
    calc
      _ = ∫ x in (0:ℝ)..1,
          (2 : ℂ) * ((f x : ℂ) *
            (Real.cos (Real.pi * ((m+1:ℕ):ℝ) * x) : ℂ)) := by
        apply intervalIntegral.integral_congr
        intro x hx
        change (bflatModePhase m x + bflatModePhase m (-x)) * (f x : ℂ) = _
        rw [(bflat_phase_pair m x).2]
        ring
      _ = _ := by rw [intervalIntegral.integral_const_mul]
  calc
    _ = (1/2:ℝ) • ∫ x in (0:ℝ)..2,
          bflatModePhase m x * (bflatEvenExtension f x : ℂ) := by
      rw [fourierCoeffOn_eq_integral]
      congr 1
      · norm_num
      · apply intervalIntegral.integral_congr
        intro x hx
        simp [bflatModePhase, smul_eq_mul]
    _ = (1/2:ℝ) •
          (2 * (∫ x in (0:ℝ)..1,
            (f x : ℂ) * (Real.cos (Real.pi * ((m+1:ℕ):ℝ) * x) : ℂ))) := by
      rw [hfold, htrig]
    _ = _ := by norm_num [smul_eq_mul]; ring

private theorem bflat_extension_integral {f : ℝ → ℝ} {C : ℝ}
    (hf : Continuous f) (hbound : ∀ x, |f x| ≤ C) (odd : Bool) :
    (∫ x in (0:ℝ)..2, (bflatExtension f odd x : ℂ)) =
      (if odd then 0 else 2 * ∫ x in (0:ℝ)..1, (f x : ℂ)) := by
  classical
  have hfmeas : Measurable f := hf.measurable
  have hmeas : Measurable (bflatExtension f odd) := by
    cases odd with
    | true =>
        change Measurable (bflatOddExtension f)
        unfold bflatOddExtension
        exact Measurable.ite measurableSet_Icc hfmeas
          (Measurable.ite measurableSet_Ioc
            (measurable_neg.comp (hfmeas.comp (measurable_const.sub measurable_id)))
            measurable_const)
    | false =>
        change Measurable (bflatEvenExtension f)
        unfold bflatEvenExtension
        exact Measurable.ite measurableSet_Icc hfmeas
          (Measurable.ite measurableSet_Ioc
            (hfmeas.comp (measurable_const.sub measurable_id)) measurable_const)
  have hboundExt (x : ℝ) : |bflatExtension f odd x| ≤ C := by
    have hb := bflat_extension_bound f C hbound x
    cases odd with
    | true => simpa [bflatExtension] using hb.1
    | false => simpa [bflatExtension] using hb.2
  have hInt {a b : ℝ} (hab : a ≤ b) :
      IntervalIntegrable (fun x => (bflatExtension f odd x : ℂ)) volume a b :=
    bflat_intervalIntegrable_of_bound
      (Complex.measurable_ofReal.comp hmeas)
      (fun x => by
        change ‖(bflatExtension f odd x : ℂ)‖ ≤ C
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact hboundExt x) hab
  have hleft : (∫ x in (0:ℝ)..1, (bflatExtension f odd x : ℂ)) =
      ∫ x in (0:ℝ)..1, (f x : ℂ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hx' : x ∈ Icc (0:ℝ) 1 := by simpa using hx
    cases odd <;> simp [bflatExtension, bflatEvenExtension, bflatOddExtension, hx']
  have hright : (∫ x in (1:ℝ)..2, (bflatExtension f odd x : ℂ)) =
      ∫ x in (1:ℝ)..2,
        (((if odd then -1 else 1 : ℝ) * f (2-x) : ℝ) : ℂ) := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro x hx
    have hx' : x ∈ Ioc (1:ℝ) 2 := ⟨hx.1, hx.2.le⟩
    have hxNot : x ∉ Icc (0:ℝ) 1 := by
      intro hh
      exact (not_le_of_gt hx.1) hh.2
    cases odd <;> simp [bflatExtension, bflatEvenExtension, bflatOddExtension,
      hxNot, hx']
  have hreflect :
      (∫ x in (1:ℝ)..2,
        (((if odd then -1 else 1 : ℝ) * f (2-x) : ℝ) : ℂ)) =
      ∫ x in (0:ℝ)..1,
        (((if odd then -1 else 1 : ℝ) * f x : ℝ) : ℂ) := by
    have hcomp := intervalIntegral.integral_comp_sub_left
      (fun x : ℝ => (((if odd then -1 else 1 : ℝ) * f x : ℝ) : ℂ))
      (a := (1:ℝ)) (b := 2) 2
    simpa only [sub_self, sub_zero, show (2:ℝ)-1=1 by norm_num] using hcomp
  calc
    _ = (∫ x in (0:ℝ)..1, (bflatExtension f odd x : ℂ)) +
          ∫ x in (1:ℝ)..2, (bflatExtension f odd x : ℂ) :=
      (intervalIntegral.integral_add_adjacent_intervals (hInt (by norm_num))
        (hInt (by norm_num))).symm
    _ = (∫ x in (0:ℝ)..1, (f x : ℂ)) +
          ∫ x in (0:ℝ)..1,
            (((if odd then -1 else 1 : ℝ) * f x : ℝ) : ℂ) := by
      rw [hleft, hright, hreflect]
    _ = _ := by
      cases odd with
      | true => simp [intervalIntegral.integral_const_mul]
      | false => simp [intervalIntegral.integral_const_mul]; ring

private theorem bflat_odd_fourierCoeffOn_zero {f : ℝ → ℝ} {C : ℝ}
    (hf : Continuous f) (hbound : ∀ x, |f x| ≤ C) :
    fourierCoeffOn (show (0:ℝ) < 2 by norm_num)
        (fun x => (bflatOddExtension f x : ℂ)) 0 = 0 := by
  rw [fourierCoeffOn_eq_integral]
  simp only [neg_zero, fourier_zero, one_smul]
  have hInt := bflat_extension_integral hf hbound true
  change (1 / (2 - 0) : ℝ) •
    (∫ x in (0:ℝ)..2, (bflatExtension f true x : ℂ)) = 0
  rw [hInt]
  norm_num

private theorem bflat_even_fourierCoeffOn_zero {f : ℝ → ℝ} {C : ℝ}
    (hf : Continuous f) (hbound : ∀ x, |f x| ≤ C) :
    fourierCoeffOn (show (0:ℝ) < 2 by norm_num)
        (fun x => (bflatEvenExtension f x : ℂ)) 0 =
      ∫ x in (0:ℝ)..1, (f x : ℂ) := by
  rw [fourierCoeffOn_eq_integral]
  simp only [neg_zero, fourier_zero, one_smul]
  have hInt := bflat_extension_integral hf hbound false
  change (1 / (2 - 0) : ℝ) •
    (∫ x in (0:ℝ)..2, (bflatExtension f false x : ℂ)) =
      ∫ x in (0:ℝ)..1, (f x : ℂ)
  rw [hInt]
  norm_num
  ring

private theorem bflat_extension_normSq_integral {f : ℝ → ℝ} {C : ℝ}
    (hf : Continuous f) (hbound : ∀ x, |f x| ≤ C) (odd : Bool) :
    (∫ x in (0:ℝ)..2, ‖(bflatExtension f odd x : ℂ)‖ ^ 2) =
      2 * ∫ x in (0:ℝ)..1, f x ^ 2 := by
  let f2 : ℝ → ℝ := fun x => f x ^ 2
  have hf2 : Continuous f2 := by
    change Continuous (fun x => f x ^ 2)
    exact hf.pow 2
  have hbound2 (x : ℝ) : |f2 x| ≤ C^2 := by
    dsimp [f2]
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg (f x)) (hbound x) 2
  have hpoint (x : ℝ) :
      ‖(bflatExtension f odd x : ℂ)‖ ^ 2 = bflatEvenExtension f2 x := by
    cases odd <;>
      simp [bflatExtension, bflatOddExtension, bflatEvenExtension,
        f2, Complex.norm_real, Real.norm_eq_abs]
  have hreal : (∫ x in (0:ℝ)..2, bflatEvenExtension f2 x) =
      2 * ∫ x in (0:ℝ)..1, f2 x := by
    have hc := bflat_extension_integral hf2 hbound2 false
    have hc' : (∫ x in (0:ℝ)..2, (bflatEvenExtension f2 x : ℂ)) =
        2 * ∫ x in (0:ℝ)..1, (f2 x : ℂ) := by
      simpa [bflatExtension] using hc
    rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal] at hc'
    norm_cast at hc'
  calc
    _ = ∫ x in (0:ℝ)..2, bflatEvenExtension f2 x := by
      apply intervalIntegral.integral_congr
      intro x hx
      exact hpoint x
    _ = 2 * ∫ x in (0:ℝ)..1, f x ^ 2 := by
      simpa [f2] using hreal

private theorem bflat_intervalIntegral_complex_ofReal_mul
    (f g : ℝ → ℝ) :
    (∫ x in (0:ℝ)..1, (f x : ℂ) * (g x : ℂ)) =
      (∫ x in (0:ℝ)..1, f x * g x : ℝ) := by
  calc
    _ = ∫ x in (0:ℝ)..1, ((f x * g x : ℝ) : ℂ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      simp
    _ = _ := intervalIntegral.integral_ofReal

private theorem bflat_odd_fourierCoeffOn_pos_real {f : ℝ → ℝ} {C : ℝ}
    (hf : Continuous f) (hbound : ∀ x, |f x| ≤ C) (m : ℕ) :
    fourierCoeffOn (show (0:ℝ) < 2 by norm_num)
        (fun x => (bflatOddExtension f x : ℂ)) ((m+1:ℕ):ℤ) =
      -Complex.I *
        ((∫ x in (0:ℝ)..1, f x * Real.sin (Real.pi * ((m+1:ℕ):ℝ) * x) : ℝ) : ℂ) := by
  rw [bflat_odd_fourierCoeffOn_pos hf hbound m,
    bflat_intervalIntegral_complex_ofReal_mul]

private theorem bflat_even_fourierCoeffOn_pos_real {f : ℝ → ℝ} {C : ℝ}
    (hf : Continuous f) (hbound : ∀ x, |f x| ≤ C) (m : ℕ) :
    fourierCoeffOn (show (0:ℝ) < 2 by norm_num)
        (fun x => (bflatEvenExtension f x : ℂ)) ((m+1:ℕ):ℤ) =
      ((∫ x in (0:ℝ)..1, f x * Real.cos (Real.pi * ((m+1:ℕ):ℝ) * x) : ℝ) : ℂ) := by
  rw [bflat_even_fourierCoeffOn_pos hf hbound m,
    bflat_intervalIntegral_complex_ofReal_mul]

/-- Parseval's identity for the normalized sine basis on `(0,1)`. -/
theorem bflatSineParsevalInterval {f : ℝ → ℝ} {C : ℝ}
    (hf : Continuous f) (hbound : ∀ x, |f x| ≤ C) :
    2 * (∑' m : ℕ,
      (∫ x in (0:ℝ)..1, f x * Real.sin (Real.pi * ((m+1:ℕ):ℝ) * x) : ℝ)^2) =
      ∫ x in (0:ℝ)..1, f x ^ 2 := by
  let h : (0:ℝ) < 2 := by norm_num
  let F : ℝ → ℂ := fun x => (bflatOddExtension f x : ℂ)
  let c : ℤ → ℝ := fun n => ‖fourierCoeffOn h F n‖ ^ 2
  have hC0 : 0 ≤ C := le_trans (abs_nonneg (f 0)) (hbound 0)
  have hL2 : MemLp F 2 (volume.restrict (Ioc (0:ℝ) 2)) := by
    simpa [F] using bflat_odd_extension_memLp hf.measurable hC0 hbound
  have hhas := hasSum_sq_fourierCoeffOn h hL2
  have hsum : Summable c := by simpa [c, F] using hhas.summable
  have heven : Function.Even c := by
    intro n
    dsimp [c]
    rw [bflat_fourierCoeffOn_neg_conj h (by intro x; simp [F]) n]
    simp
  have hparseval : ∑' n : ℤ, c n =
      ((2:ℝ) - 0)⁻¹ • ∫ x in (0:ℝ)..2, ‖F x‖ ^ 2 := by
    simpa [c, F] using hhas.tsum_eq
  have hzero : c 0 = 0 := by
    dsimp [c, F]
    rw [bflat_odd_fourierCoeffOn_zero hf hbound]
    simp
  have hpos (m : ℕ) : c ((m+1:ℕ):ℤ) =
      (∫ x in (0:ℝ)..1, f x * Real.sin (Real.pi * ((m+1:ℕ):ℝ) * x) : ℝ)^2 := by
    dsimp [c, F]
    have hidx : ((m+1:ℕ):ℤ) = (m:ℤ) + 1 := by norm_cast
    rw [← hidx, bflat_odd_fourierCoeffOn_pos_real hf hbound m]
    simp
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat heven hsum] at hparseval
  have hpnat : (∑' n : ℕ+, c ↑↑n) = ∑' m : ℕ, c ((m+1:ℕ):ℤ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tsum_pnat_eq_tsum_succ (f := fun m : ℕ => c (m:ℤ)))
  rw [hpnat] at hparseval
  rw [hzero] at hparseval
  simp_rw [hpos] at hparseval
  have hnorm : ∫ x in (0:ℝ)..2, ‖F x‖ ^ 2 =
      2 * ∫ x in (0:ℝ)..1, f x ^ 2 := by
    simpa [F, bflatExtension] using bflat_extension_normSq_integral hf hbound true
  rw [hnorm] at hparseval
  norm_num [smul_eq_mul] at hparseval
  ring_nf at hparseval
  have hterm (m : ℕ) :
      (∫ x in (0:ℝ)..1, f x * Real.sin (Real.pi * (m:ℝ) * x + Real.pi*x) : ℝ)^2 =
      (∫ x in (0:ℝ)..1, f x * Real.sin (Real.pi * ((m+1:ℕ):ℝ) * x) : ℝ)^2 := by
    apply congrArg (fun z : ℝ => z ^ 2)
    apply intervalIntegral.integral_congr_ae
    filter_upwards [] with x
    intro _
    congr 1
    push_cast
    ring_nf
  have hsumchange :
      (∑' m : ℕ, (∫ x in (0:ℝ)..1,
        f x * Real.sin (Real.pi * (m:ℝ) * x + Real.pi*x) : ℝ)^2) =
      ∑' m : ℕ, (∫ x in (0:ℝ)..1,
        f x * Real.sin (Real.pi * ((m+1:ℕ):ℝ) * x) : ℝ)^2 :=
    tsum_congr hterm
  calc
    2 * (∑' m : ℕ, (∫ x in (0:ℝ)..1,
        f x * Real.sin (Real.pi * ((m+1:ℕ):ℝ) * x) : ℝ)^2) =
      (∑' m : ℕ, (∫ x in (0:ℝ)..1,
        f x * Real.sin (Real.pi * (m:ℝ) * x + Real.pi*x) : ℝ)^2) * 2 := by
          rw [← hsumchange]
          ring
    _ = ∫ x in (0:ℝ)..1, f x ^ 2 := by simpa [add_comm] using hparseval

/-- Parseval's identity for the constant and positive cosine modes on `(0,1)`. -/
theorem bflatCosineParsevalInterval {f : ℝ → ℝ} {C : ℝ}
    (hf : Continuous f) (hbound : ∀ x, |f x| ≤ C) :
    (∫ x in (0:ℝ)..1, f x : ℝ)^2 +
      2 * (∑' m : ℕ,
        (∫ x in (0:ℝ)..1, f x * Real.cos (Real.pi * ((m+1:ℕ):ℝ) * x) : ℝ)^2) =
      ∫ x in (0:ℝ)..1, f x ^ 2 := by
  let h : (0:ℝ) < 2 := by norm_num
  let F : ℝ → ℂ := fun x => (bflatEvenExtension f x : ℂ)
  let c : ℤ → ℝ := fun n => ‖fourierCoeffOn h F n‖ ^ 2
  have hC0 : 0 ≤ C := le_trans (abs_nonneg (f 0)) (hbound 0)
  have hL2 : MemLp F 2 (volume.restrict (Ioc (0:ℝ) 2)) := by
    simpa [F] using bflat_even_extension_memLp hf.measurable hC0 hbound
  have hhas := hasSum_sq_fourierCoeffOn h hL2
  have hsum : Summable c := by simpa [c, F] using hhas.summable
  have heven : Function.Even c := by
    intro n
    dsimp [c]
    rw [bflat_fourierCoeffOn_neg_conj h (by intro x; simp [F]) n]
    simp
  have hparseval : ∑' n : ℤ, c n =
      ((2:ℝ) - 0)⁻¹ • ∫ x in (0:ℝ)..2, ‖F x‖ ^ 2 := by
    simpa [c, F] using hhas.tsum_eq
  have hzero : c 0 = (∫ x in (0:ℝ)..1, f x : ℝ)^2 := by
    dsimp [c, F]
    rw [bflat_even_fourierCoeffOn_zero hf hbound]
    rw [intervalIntegral.integral_ofReal]
    simp [Complex.norm_real, Real.norm_eq_abs]
  have hpos (m : ℕ) : c ((m+1:ℕ):ℤ) =
      (∫ x in (0:ℝ)..1, f x * Real.cos (Real.pi * ((m+1:ℕ):ℝ) * x) : ℝ)^2 := by
    dsimp [c, F]
    have hidx : ((m+1:ℕ):ℤ) = (m:ℤ) + 1 := by norm_cast
    rw [← hidx, bflat_even_fourierCoeffOn_pos_real hf hbound m]
    simp
  rw [tsum_int_eq_zero_add_two_mul_tsum_pnat heven hsum] at hparseval
  have hpnat : (∑' n : ℕ+, c ↑↑n) = ∑' m : ℕ, c ((m+1:ℕ):ℤ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tsum_pnat_eq_tsum_succ (f := fun m : ℕ => c (m:ℤ)))
  rw [hpnat] at hparseval
  rw [hzero] at hparseval
  simp_rw [hpos] at hparseval
  have hnorm : ∫ x in (0:ℝ)..2, ‖F x‖ ^ 2 =
      2 * ∫ x in (0:ℝ)..1, f x ^ 2 := by
    simpa [F, bflatExtension] using bflat_extension_normSq_integral hf hbound false
  rw [hnorm] at hparseval
  norm_num [smul_eq_mul] at hparseval
  ring_nf at hparseval
  have hterm (m : ℕ) :
      (∫ x in (0:ℝ)..1, f x * Real.cos (Real.pi * (m:ℝ) * x + Real.pi*x) : ℝ)^2 =
      (∫ x in (0:ℝ)..1, f x * Real.cos (Real.pi * ((m+1:ℕ):ℝ) * x) : ℝ)^2 := by
    apply congrArg (fun z : ℝ => z ^ 2)
    apply intervalIntegral.integral_congr_ae
    filter_upwards [] with x
    intro _
    congr 1
    push_cast
    ring_nf
  have hsumchange :
      (∑' m : ℕ, (∫ x in (0:ℝ)..1,
        f x * Real.cos (Real.pi * (m:ℝ) * x + Real.pi*x) : ℝ)^2) =
      ∑' m : ℕ, (∫ x in (0:ℝ)..1,
        f x * Real.cos (Real.pi * ((m+1:ℕ):ℝ) * x) : ℝ)^2 :=
    tsum_congr hterm
  calc
    (∫ x in (0:ℝ)..1, f x : ℝ)^2 +
        2 * (∑' m : ℕ, (∫ x in (0:ℝ)..1,
          f x * Real.cos (Real.pi * ((m+1:ℕ):ℝ) * x) : ℝ)^2) =
      (∑' m : ℕ, (∫ x in (0:ℝ)..1,
        f x * Real.cos (Real.pi * (m:ℝ) * x + Real.pi*x) : ℝ)^2) * 2 +
          (∫ x in (0:ℝ)..1, f x : ℝ)^2 := by
            rw [← hsumchange]
            ring
    _ = ∫ x in (0:ℝ)..1, f x ^ 2 := by simpa [add_comm] using hparseval

/-- The squared sine coefficients in `bflatSineParsevalInterval` are summable. -/
theorem bflatSineModeCoefficients_summable {f : ℝ → ℝ} {C : ℝ}
    (hf : Continuous f) (hbound : ∀ x, |f x| ≤ C) :
    Summable (fun m : ℕ =>
      (∫ x in (0:ℝ)..1, f x * Real.sin (Real.pi * ((m+1:ℕ):ℝ) * x) : ℝ)^2) := by
  let h : (0:ℝ) < 2 := by norm_num
  let F : ℝ → ℂ := fun x => (bflatOddExtension f x : ℂ)
  let c : ℤ → ℝ := fun n => ‖fourierCoeffOn h F n‖ ^ 2
  have hC0 : 0 ≤ C := le_trans (abs_nonneg (f 0)) (hbound 0)
  have hL2 : MemLp F 2 (volume.restrict (Ioc (0:ℝ) 2)) := by
    simpa [F] using bflat_odd_extension_memLp hf.measurable hC0 hbound
  have hhas := hasSum_sq_fourierCoeffOn h hL2
  have hsum : Summable c := by simpa [c, F] using hhas.summable
  have hpos (m : ℕ) : c ((m+1:ℕ):ℤ) =
      (∫ x in (0:ℝ)..1, f x * Real.sin (Real.pi * ((m+1:ℕ):ℝ) * x) : ℝ)^2 := by
    dsimp [c, F]
    have hidx : ((m+1:ℕ):ℤ) = (m:ℤ) + 1 := by norm_cast
    rw [← hidx, bflat_odd_fourierCoeffOn_pos_real hf hbound m]
    simp
  have hi : Function.Injective (fun m : ℕ => ((m+1:ℕ):ℤ)) := by
    intro m n hmn
    exact Nat.add_right_cancel (Int.ofNat.inj hmn)
  exact (hsum.comp_injective hi).congr hpos

/-- The squared cosine coefficients in `bflatCosineParsevalInterval` are summable. -/
theorem bflatCosineModeCoefficients_summable {f : ℝ → ℝ} {C : ℝ}
    (hf : Continuous f) (hbound : ∀ x, |f x| ≤ C) :
    Summable (fun m : ℕ =>
      (∫ x in (0:ℝ)..1, f x * Real.cos (Real.pi * ((m+1:ℕ):ℝ) * x) : ℝ)^2) := by
  let h : (0:ℝ) < 2 := by norm_num
  let F : ℝ → ℂ := fun x => (bflatEvenExtension f x : ℂ)
  let c : ℤ → ℝ := fun n => ‖fourierCoeffOn h F n‖ ^ 2
  have hC0 : 0 ≤ C := le_trans (abs_nonneg (f 0)) (hbound 0)
  have hL2 : MemLp F 2 (volume.restrict (Ioc (0:ℝ) 2)) := by
    simpa [F] using bflat_even_extension_memLp hf.measurable hC0 hbound
  have hhas := hasSum_sq_fourierCoeffOn h hL2
  have hsum : Summable c := by simpa [c, F] using hhas.summable
  have hpos (m : ℕ) : c ((m+1:ℕ):ℤ) =
      (∫ x in (0:ℝ)..1, f x * Real.cos (Real.pi * ((m+1:ℕ):ℝ) * x) : ℝ)^2 := by
    dsimp [c, F]
    have hidx : ((m+1:ℕ):ℤ) = (m:ℤ) + 1 := by norm_cast
    rw [← hidx, bflat_even_fourierCoeffOn_pos_real hf hbound m]
    simp
  have hi : Function.Injective (fun m : ℕ => ((m+1:ℕ):ℤ)) := by
    intro m n hmn
    exact Nat.add_right_cancel (Int.ofNat.inj hmn)
  exact (hsum.comp_injective hi).congr hpos

end ASDExplicitGamma.Model
