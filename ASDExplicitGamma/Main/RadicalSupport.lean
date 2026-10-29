module

public import ASDExplicitGamma.Main.RadicalProfile
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Exact tangent slopes for the source error-profile radicals. -/

@[expose] public section

namespace ASDExplicitGamma.Main

/-- The positive supporting slope at an interior anchor. -/
noncomputable def mainRadicalSlope {ι : Type*} [Fintype ι]
    (slope : ℝ) (weight offset rate : ι → ℝ) (anchor : ℝ) : ℝ :=
  slope + ∑ i, weight i * rate i / (2 * Real.sqrt (offset i - rate i * anchor))

/-- The profile has its ordinary derivative at every point at which
all radicands are strictly positive. -/
theorem mainRadicalProfile_hasDerivAt {ι : Type*} [Fintype ι]
    (c slope : ℝ) (weight offset rate : ι → ℝ) (anchor : ℝ)
    (hanchor : ∀ i, 0 < offset i - rate i * anchor) :
    HasDerivAt (mainRadicalProfile c slope weight offset rate)
      (-mainRadicalSlope slope weight offset rate anchor) anchor := by
  have hroot (i : ι) : HasDerivAt
      (fun f => weight i * Real.sqrt (offset i - rate i * f))
      (weight i * (-rate i / (2 * Real.sqrt (offset i - rate i * anchor)))) anchor := by
    simpa only [zero_sub, mul_one, Pi.sub_apply, id_eq] using (((hasDerivAt_const anchor (offset i)).sub
      ((hasDerivAt_id anchor).const_mul (rate i))).sqrt (hanchor i).ne').const_mul (weight i)
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hroot i)
  have hl := (hasDerivAt_const anchor c).sub ((hasDerivAt_id anchor).const_mul slope)
  have heq : -mainRadicalSlope slope weight offset rate anchor =
      (0 - slope * 1) + ∑ i, weight i * (-rate i / (2*Real.sqrt (offset i-rate i*anchor))) := by
    simp only [mainRadicalSlope, zero_sub, mul_one, neg_add, neg_div, mul_neg,
      Finset.sum_neg_distrib, mul_div_assoc]
  rw [heq]
  exact hl.add hs

theorem mainRadicalSlope_pos {ι : Type*} [Fintype ι]
    (slope : ℝ) (weight offset rate : ι → ℝ) (anchor : ℝ)
    (hs : 0 < slope) (hw : ∀ i, 0 ≤ weight i) (hr : ∀ i, 0 ≤ rate i) :
    0 < mainRadicalSlope slope weight offset rate anchor := by
  apply add_pos_of_pos_of_nonneg hs
  exact Finset.sum_nonneg fun i _ => div_nonneg (mul_nonneg (hw i) (hr i))
    (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))

/-- The exact tangent inequality for a square root, valid at boundary
values of its argument and a strictly interior anchor. -/
theorem main_sqrt_support (x y : ℝ) (hx : 0 ≤ x) (hy : 0 < y) :
    Real.sqrt x ≤ Real.sqrt y + (x-y)/(2*Real.sqrt y) := by
  have hsy := Real.sqrt_pos.mpr hy
  have hsx := Real.sq_sqrt hx
  have hsy2 := Real.sq_sqrt hy.le
  apply (mul_le_mul_iff_left₀ (by positivity : 0 < 2 * Real.sqrt y)).mp
  have heq : (Real.sqrt y + (x-y)/(2*Real.sqrt y))*(2*Real.sqrt y) =
      2*y+x-y := by field_simp; nlinarith only [hsy2]
  rw [heq]
  nlinarith only [hsx, hsy2, sq_nonneg (Real.sqrt x - Real.sqrt y)]

/-- The literal supporting line, with no differentiation or concavity
hypothesis added to the profile. -/
theorem mainRadicalProfile_support {ι : Type*} [Fintype ι]
    (c slope : ℝ) (weight offset rate : ι → ℝ) (anchor f : ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hf : f ∈ mainRadicalDomain offset rate)
    (hanchor : ∀ i, 0 < offset i - rate i * anchor) :
    mainRadicalProfile c slope weight offset rate f ≤
      mainRadicalProfile c slope weight offset rate anchor +
        mainRadicalSlope slope weight offset rate anchor * (anchor-f) := by
  have hroot (i : ι) : weight i * Real.sqrt (offset i-rate i*f) ≤
      weight i * Real.sqrt (offset i-rate i*anchor) +
        (weight i*rate i/(2*Real.sqrt (offset i-rate i*anchor)))*(anchor-f) := by
    have h := mul_le_mul_of_nonneg_left
      (main_sqrt_support _ _ (hf i) (hanchor i)) (hw i)
    convert h using 1
    ring
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun i _ => hroot i
  rw [Finset.sum_add_distrib, ← Finset.sum_mul] at hsum
  unfold mainRadicalProfile mainRadicalSlope
  linarith only [hsum]

end ASDExplicitGamma.Main
