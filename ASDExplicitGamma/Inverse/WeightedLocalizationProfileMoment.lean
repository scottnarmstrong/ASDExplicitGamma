module

public import ASDExplicitGamma.Inverse.WeightedLocalizationProfile
public import Mathlib.Analysis.SpecificLimits.Normed

/-! Exact first profile moment, needed for the retained x-weighted PE errors. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

/-- The source's profile-weighted rational generating function Tf. -/
noncomputable def localizationProfileTf (a z : ℝ) : ℝ :=
  (2 * a * z ^ 2 + 3 * a ^ 2 * z ^ 3 + 4 * a ^ 3 * z ^ 4) / (1 - a ^ 3 * z ^ 4) +
    4 * a ^ 3 * z ^ 4 * (a * z ^ 2 + a ^ 2 * z ^ 3 + a ^ 3 * z ^ 4) / (1 - a ^ 3 * z ^ 4) ^ 2

/-- The complete first moment of the literal ceil-profile, with its four-step
residue ratio and exact rational denominator. -/
theorem localization_profile_moment_hasSum (a z : ℝ) (ha : 0 ≤ a) (hz : 0 ≤ z)
    (hsmall : a ^ 3 * z ^ 4 < 1) :
    HasSum (fun n : ℕ => (localizationProfileDepth (n + 1) : ℝ) *
      a ^ (n + 1) * z ^ localizationProfileDepth (n + 1)) (localizationProfileTf a z) := by
  let q := a ^ 3 * z ^ 4
  let C := a * z ^ 2 + a ^ 2 * z ^ 3 + a ^ 3 * z ^ 4
  let D := 2 * a * z ^ 2 + 3 * a ^ 2 * z ^ 3 + 4 * a ^ 3 * z ^ 4
  let f : ℕ × Fin 3 → ℝ := fun p =>
    ((4 * p.1 + p.2.1 + 2 : ℕ) : ℝ) * (a ^ (p.2.1 + 1) * z ^ (p.2.1 + 2)) * q ^ p.1
  have hg := hasSum_geometric_of_lt_one (by positivity : 0 ≤ q) hsmall
  have hm := hasSum_coe_mul_geometric_of_norm_lt_one (r := q)
    (by rw [Real.norm_of_nonneg (by positivity : 0 ≤ q)]; exact hsmall)
  have hinner : HasSum (fun t : ℕ => ∑ r : Fin 3, f (t, r)) (localizationProfileTf a z) := by
    convert (hg.mul_left D).add (hm.mul_left (4 * C)) using 1
    · funext t
      dsimp only [f, C, D]
      simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ]
      push_cast
      norm_num
      ring
    · dsimp only [C, D, q, localizationProfileTf]
      ring
  have hsum : Summable f := (summable_prod_of_nonneg (by intro p; dsimp only [f, q]; positivity)).mpr
    ⟨fun t => (hasSum_fintype (fun r : Fin 3 => f (t, r))).summable,
      by simpa only [tsum_fintype] using hinner.summable⟩
  have hprod := hsum.hasSum.prod_fiberwise (fun t => hasSum_fintype (fun r : Fin 3 => f (t, r)))
  have hfull : HasSum f (localizationProfileTf a z) := (hprod.unique hinner) ▸ hsum.hasSum
  apply (Nat.divModEquiv 3).symm.hasSum_iff.mp
  convert hfull using 1
  funext p
  change (localizationProfileDepth (p.1 * 3 + p.2.1 + 1) : ℝ) *
    a ^ (p.1 * 3 + p.2.1 + 1) * z ^ localizationProfileDepth (p.1 * 3 + p.2.1 + 1) = f p
  rw [Nat.mul_comm p.1 3, mul_assoc, localization_profile_term, localization_profile_residue]
  dsimp only [f, q]
  ring

end ASDExplicitGamma.Inverse
