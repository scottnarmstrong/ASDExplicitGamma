module

public import ASDExplicitGamma.Numerics.Model.ProjectionIdentity
public import ASDExplicitGamma.Model.BflatCovariance
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! # Modal algebra for the q3 flat harmonic tail

This module isolates the one-dimensional Parseval step used by the source tail.
The public source theorem will apply it after identifying the actual Dirichlet
projection with its covariance-mode series.
-/

@[expose] public section

namespace ASDExplicitGamma.Model

open ASDExplicitGamma.Numerics.Model

private theorem modeWeight_nonneg (m n : ℕ) : 0 ≤ modeWeight m n := by
  unfold modeWeight
  positivity

private theorem modeWeight_le_one (m n : ℕ) : modeWeight m n ≤ 1 := by
  have hden : 0 < ((m + 1 : ℕ) : ℝ) ^ 2 + ((n + 1 : ℕ) : ℝ) ^ 2 := by
    positivity
  have hnum : ((m + 1 : ℕ) : ℝ) ^ 2 ≤
      ((m + 1 : ℕ) : ℝ) ^ 2 + ((n + 1 : ℕ) : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (((n + 1 : ℕ) : ℝ))]
  unfold modeWeight
  exact (div_le_one hden).2 hnum

private theorem summable_pair_product {f g : ℕ → ℝ}
    (hf : Summable f) (hg : Summable g)
    (hf0 : ∀ n, 0 ≤ f n) (hg0 : ∀ n, 0 ≤ g n) :
    Summable (fun p : ℕ × ℕ => f p.1 * g p.2) := by
  apply (summable_prod_of_nonneg (f := fun p : ℕ × ℕ => f p.1 * g p.2)
    (fun p => mul_nonneg (hf0 p.1) (hg0 p.2))).2
  constructor
  · intro m
    exact hg.mul_left (f m)
  · have hrow : (fun m : ℕ => ∑' n : ℕ, f m * g n) =
        (fun m => f m * ∑' n : ℕ, g n) := by
      funext m
      rw [tsum_mul_left]
    rw [hrow]
    exact hf.mul_right _

private theorem weighted_pair_summable {f g : ℕ → ℝ}
    (hf : Summable f) (hg : Summable g)
    (hf0 : ∀ n, 0 ≤ f n) (hg0 : ∀ n, 0 ≤ g n) :
    Summable (fun p : ℕ × ℕ => modeWeight p.1 p.2 * (f p.1 * g p.2)) := by
  apply Summable.of_nonneg_of_le
    (fun p => mul_nonneg (modeWeight_nonneg p.1 p.2)
      (mul_nonneg (hf0 p.1) (hg0 p.2)))
    (fun p => by
      have h := modeWeight_le_one p.1 p.2
      have hfg := mul_nonneg (hf0 p.1) (hg0 p.2)
      nlinarith [mul_le_mul_of_nonneg_right h hfg])
    (summable_pair_product hf hg hf0 hg0)

/-- The symmetric Dirichlet weights divide the product of two sine-mode
covariance masses exactly in half. -/
private theorem weighted_sine_square_eq_half {s : ℕ → ℝ}
    (hs : Summable s) (hs0 : ∀ n, 0 ≤ s n) (hsum : ∑' n, s n = 1) :
    (∑' p : ℕ × ℕ, modeWeight p.1 p.2 * (s p.1 * s p.2)) = 1 / 2 := by
  have hpair := weighted_pair_summable hs hs hs0 hs0
  have hswap : (∑' p : ℕ × ℕ,
      modeWeight p.1 p.2 * (s p.1 * s p.2)) =
      ∑' p : ℕ × ℕ, modeWeight p.2 p.1 * (s p.1 * s p.2) := by
    calc
      _ = ∑' p : ℕ × ℕ,
          modeWeight p.2 p.1 * (s p.2 * s p.1) :=
            (Equiv.prodComm ℕ ℕ).tsum_eq _
      _ = _ := by
        apply tsum_congr
        intro p
        ring
  have hsumprod : (∑' n, s n) * (∑' n, s n) =
      ∑' p : ℕ × ℕ, s p.1 * s p.2 := by
    rw [hs.tsum_mul_tsum hs (summable_pair_product hs hs hs0 hs0)]
  have hweighted :
      (∑' p : ℕ × ℕ, modeWeight p.1 p.2 * (s p.1 * s p.2)) +
      (∑' p : ℕ × ℕ, modeWeight p.2 p.1 * (s p.1 * s p.2)) =
      ∑' p : ℕ × ℕ, s p.1 * s p.2 := by
    have hpairSwap : Summable (fun p : ℕ × ℕ =>
        modeWeight p.2 p.1 * (s p.1 * s p.2)) := by
      apply Summable.of_nonneg_of_le
        (fun p => mul_nonneg (modeWeight_nonneg p.2 p.1)
          (mul_nonneg (hs0 p.1) (hs0 p.2)))
        (fun p => by
          have h := modeWeight_le_one p.2 p.1
          have hprod := mul_nonneg (hs0 p.1) (hs0 p.2)
          have hle := mul_le_mul_of_nonneg_right h hprod
          simpa only [one_mul] using hle)
        (summable_pair_product hs hs hs0 hs0)
    calc
      _ = ∑' p : ℕ × ℕ,
          (modeWeight p.1 p.2 * (s p.1 * s p.2) +
            modeWeight p.2 p.1 * (s p.1 * s p.2)) :=
              (hpair.tsum_add hpairSwap).symm
      _ = _ := by
        apply tsum_congr
        intro p
        rw [← add_mul, mode_weight_symmetry, one_mul]
  rw [hsum] at hsumprod
  rw [hswap] at hweighted
  nlinarith [hsumprod]

/-- Conditional scalar-series form of the source's all-depth flat harmonic
bound. `s` and `d` are respectively the sine covariance masses and their
sine-minus-cosine differences. -/
theorem bflat_modal_tail_bound {s d : ℕ → ℝ} {c : ℝ}
    (hs : Summable s) (hd : Summable d)
    (hs0 : ∀ n, 0 ≤ s n) (hd0 : ∀ n, 0 ≤ d n)
    (hds : ∀ n, d n ≤ s n)
    (hsum : ∑' n, s n = 1) (hdSum : ∑' n, d n = c) :
    2 - 4 * (∑' p : ℕ × ℕ,
        modeWeight p.1 p.2 * ((s p.1 - d p.1) * s p.2)) ≤ min 2 (4 * c) := by
  have hss := weighted_pair_summable hs hs hs0 hs0
  have hdsProd := weighted_pair_summable hd hs hd0 hs0
  have hws := weighted_pair_summable hs hs hs0 hs0
  have hwd := weighted_pair_summable hd hs hd0 hs0
  have hcss : Summable (fun p : ℕ × ℕ =>
      modeWeight p.1 p.2 * ((s p.1 - d p.1) * s p.2)) := by
    refine Summable.of_nonneg_of_le
      (fun p => mul_nonneg (modeWeight_nonneg p.1 p.2)
        (mul_nonneg (sub_nonneg.mpr (hds p.1)) (hs0 p.2)))
      (fun p => ?_) hss
    have h₁ : 0 ≤ (s p.1 - d p.1) * s p.2 :=
      mul_nonneg (sub_nonneg.mpr (hds p.1)) (hs0 p.2)
    have h₂ : (s p.1 - d p.1) * s p.2 ≤ s p.1 * s p.2 := by
      exact mul_le_mul_of_nonneg_right (sub_le_self _ (hd0 p.1)) (hs0 p.2)
    exact mul_le_mul_of_nonneg_left h₂ (modeWeight_nonneg p.1 p.2)
  have hbase := weighted_sine_square_eq_half hs hs0 hsum
  have hcorrection_le :
      (∑' p : ℕ × ℕ, modeWeight p.1 p.2 * (d p.1 * s p.2)) ≤ c := by
    have hle : ∀ p : ℕ × ℕ,
        modeWeight p.1 p.2 * (d p.1 * s p.2) ≤ d p.1 * s p.2 := by
      intro p
      have hx := mul_le_mul_of_nonneg_right (modeWeight_le_one p.1 p.2)
        (mul_nonneg (hd0 p.1) (hs0 p.2))
      simpa only [one_mul] using hx
    have hprod := summable_pair_product hd hs hd0 hs0
    calc
      _ ≤ ∑' p : ℕ × ℕ, d p.1 * s p.2 := hdsProd.tsum_le_tsum hle hprod
      _ = (∑' n, d n) * (∑' n, s n) := by
        rw [hd.tsum_mul_tsum hs (summable_pair_product hd hs hd0 hs0)]
      _ = c := by rw [hdSum, hsum, mul_one]
  have hdecomp :
      (∑' p : ℕ × ℕ, modeWeight p.1 p.2 * ((s p.1 - d p.1) * s p.2)) =
      (∑' p : ℕ × ℕ, modeWeight p.1 p.2 * (s p.1 * s p.2)) -
      (∑' p : ℕ × ℕ, modeWeight p.1 p.2 * (d p.1 * s p.2)) := by
    have hpoint : ∀ p : ℕ × ℕ,
        modeWeight p.1 p.2 * ((s p.1 - d p.1) * s p.2) =
          modeWeight p.1 p.2 * (s p.1 * s p.2) -
            modeWeight p.1 p.2 * (d p.1 * s p.2) := by
      intro p
      ring
    calc
      _ = ∑' p : ℕ × ℕ,
          (modeWeight p.1 p.2 * (s p.1 * s p.2) -
            modeWeight p.1 p.2 * (d p.1 * s p.2)) := by
              apply tsum_congr
              intro p
              exact hpoint p
      _ = _ := hws.tsum_sub hwd
  have hC_nonneg : 0 ≤ ∑' p : ℕ × ℕ,
      modeWeight p.1 p.2 * ((s p.1 - d p.1) * s p.2) :=
    tsum_nonneg fun p => mul_nonneg (modeWeight_nonneg p.1 p.2)
      (mul_nonneg (sub_nonneg.mpr (hds p.1)) (hs0 p.2))
  rw [hdecomp, hbase] at hC_nonneg
  have hB_eq : 2 - 4 * (∑' p : ℕ × ℕ,
      modeWeight p.1 p.2 * ((s p.1 - d p.1) * s p.2)) =
      4 * (∑' p : ℕ × ℕ, modeWeight p.1 p.2 * (d p.1 * s p.2)) := by
    rw [hdecomp, hbase]
    ring
  rw [hB_eq]
  apply le_min <;> nlinarith [hC_nonneg, hcorrection_le]

/-- The modal tail inequality with the explicit q3 constant covariance. This
is the one-dimensional Parseval step of MO-BFLAT-TAIL; an actual projection
consumer must still establish its sine/cosine mass hypotheses and the Bessel
comparison. -/
theorem bflat_q3_modal_tail_bound {s d : ℕ → ℝ} {ell : ℝ}
    (hs : Summable s) (hd : Summable d)
    (hs0 : ∀ n, 0 ≤ s n) (hd0 : ∀ n, 0 ≤ d n)
    (hds : ∀ n, d n ≤ s n) (hsum : ∑' n, s n = 1)
    (hdSum : ∑' n, d n =
      2*ell*(∫ u in (0 : ℝ)..1, ASDExplicitGamma.q3Cov u*(1-ell*u))) :
    2-4*(∑' p : ℕ × ℕ,
        modeWeight p.1 p.2*((s p.1-d p.1)*s p.2)) ≤
      min 2 ((429/175 : ℝ)*ell-(7/15 : ℝ)*ell^2) := by
  have h := bflat_modal_tail_bound hs hd hs0 hd0 hds hsum hdSum
  rw [ASDExplicitGamma.Model.q3Cov_flat_constant_mode] at h
  have hconst : 4*((429/700 : ℝ)*ell-(7/60 : ℝ)*ell^2) =
      (429/175 : ℝ)*ell-(7/15 : ℝ)*ell^2 := by ring
  rw [hconst] at h
  exact h

end ASDExplicitGamma.Model
