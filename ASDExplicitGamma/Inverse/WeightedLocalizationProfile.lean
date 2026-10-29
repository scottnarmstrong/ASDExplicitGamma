module

public import ASDExplicitGamma.Inverse.WhitneyLayerWeights
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Algebra.BigOperators.Fin

/-! Exact infinite generating function for k+ceil(k/3), with all three residues retained. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

/-- The deterministic reset depth before its height and fixed offsets. -/
def localizationProfileDepth (k : ℕ) : ℕ := k + (k + 2) / 3

/-- Exact residue decomposition of the source profile for k>=1. -/
theorem localization_profile_residue (t : ℕ) (r : Fin 3) :
    localizationProfileDepth (3 * t + r.1 + 1) = 4 * t + r.1 + 2 := by
  unfold localizationProfileDepth
  have hr := r.isLt
  omega

/-- The real generating function, matching the source rational expression T. -/
noncomputable def localizationProfileT (a z : ℝ) : ℝ :=
  (a * z ^ 2 + a ^ 2 * z ^ 3 + a ^ 3 * z ^ 4) / (1 - a ^ 3 * z ^ 4)

/-- Every profile term has exactly its residue coefficient and its four-step ratio. -/
theorem localization_profile_term (a z : ℝ) (t : ℕ) (r : Fin 3) :
    a ^ (3 * t + r.1 + 1) * z ^ localizationProfileDepth (3 * t + r.1 + 1) =
      (a ^ (r.1 + 1) * z ^ (r.1 + 2)) * (a ^ 3 * z ^ 4) ^ t := by
  rw [localization_profile_residue]
  have h1 : 3 * t + r.1 + 1 = 3 * t + (r.1 + 1) := by omega
  have h2 : 4 * t + r.1 + 2 = 4 * t + (r.1 + 2) := by omega
  rw [h1, h2]
  simp only [pow_add, pow_mul, mul_pow]
  ring

/-- The exact full infinite profile sum; it is neither a finite scan nor a
crude geometric envelope replacing the source ceil(k/3). -/
theorem localization_profile_hasSum (a z : ℝ) (ha : 0 ≤ a) (hz : 0 ≤ z)
    (hsmall : a ^ 3 * z ^ 4 < 1) :
    HasSum (fun n : ℕ => a ^ (n + 1) * z ^ localizationProfileDepth (n + 1))
      (localizationProfileT a z) := by
  let f : ℕ × Fin 3 → ℝ := fun p =>
    (a ^ (p.2.1 + 1) * z ^ (p.2.1 + 2)) * (a ^ 3 * z ^ 4) ^ p.1
  have hcoeff : (∑ r : Fin 3, a ^ (r.1 + 1) * z ^ (r.1 + 2)) =
      a * z ^ 2 + a ^ 2 * z ^ 3 + a ^ 3 * z ^ 4 := by
    simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ]
    norm_num
    ring
  have hinner : HasSum (fun t : ℕ => ∑ r : Fin 3, f (t, r)) (localizationProfileT a z) := by
    have hh := (hasSum_geometric_of_lt_one (by positivity : 0 ≤ a ^ 3 * z ^ 4) hsmall).mul_left
      (a * z ^ 2 + a ^ 2 * z ^ 3 + a ^ 3 * z ^ 4)
    convert hh using 1
    · funext t
      dsimp only [f]
      rw [← Finset.sum_mul, hcoeff]
    · rfl
  have hsum : Summable f := (summable_prod_of_nonneg (by intro p; dsimp only [f]; positivity)).mpr
    ⟨fun t => (hasSum_fintype (fun r : Fin 3 => f (t, r))).summable, by simpa only [tsum_fintype] using hinner.summable⟩
  have hprod := hsum.hasSum.prod_fiberwise (fun t => hasSum_fintype (fun r : Fin 3 => f (t, r)))
  have hfull : HasSum f (localizationProfileT a z) := (hprod.unique hinner) ▸ hsum.hasSum
  apply (Nat.divModEquiv 3).symm.hasSum_iff.mp
  convert hfull using 1
  funext p
  change a ^ (p.1 * 3 + p.2.1 + 1) * z ^ localizationProfileDepth (p.1 * 3 + p.2.1 + 1) = f p
  rw [Nat.mul_comm p.1 3]
  exact localization_profile_term a z p.1 p.2

end ASDExplicitGamma.Inverse
