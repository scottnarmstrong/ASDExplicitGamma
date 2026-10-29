module

public import ASDExplicitGamma.Cold.SquareSineMean
public import Mathlib.Analysis.Real.Pi.Bounds

/-! # Paying the first axial modes from the zero mean-gradient constraint -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators

namespace ASDExplicitGamma.Cold

/-- The numerical slack used in the constrained spectral estimate. -/
theorem residual_pi_sq_le_ten : Real.pi ^ 2 ≤ 10 := by
  nlinarith [Real.pi_lt_d2, Real.pi_pos]

/-- A rank-one constraint pays the two exceptional signed axial coefficients from the
higher axial modes. The profile `b` will be the Fourier coefficients of the constant function;
its support and normalization are proved from spatial integrals in the consumer. -/
theorem residual_axial_first_mode_bound {α : Type*} (a b : α → ℝ) (S : Set α)
    (l r : α) (hlr : l ≠ r) (hl : l ∉ S) (hr : r ∉ S)
    (ha : Summable (fun x => a x ^ 2))
    (hb : HasSum (fun x => b x ^ 2) 1) (hab : HasSum (fun x => a x * b x) 0)
    (har : a r = -a l) (hbl : b l = 2 / Real.pi) (hbr : b r = -2 / Real.pi)
    (hsupport : ∀ x, x ≠ l → x ≠ r → x ∉ S → b x = 0) :
    6 * a l ^ 2 ≤ ∑' x, S.indicator (fun y => a y ^ 2) x := by
  classical
  let A := ∑' x, S.indicator (fun y => a y ^ 2) x
  let B := ∑' x, S.indicator (fun y => b y ^ 2) x
  let C := ∑' x, S.indicator (fun y => a y * b y) x
  have hAs := ha.indicator S
  have hBs := hb.summable.indicator S
  have hCs := hab.summable.indicator S
  have hB : (2 / Real.pi) ^ 2 + (-2 / Real.pi) ^ 2 + B = 1 := by
    have hs := ((hasSum_ite_eq l ((2 / Real.pi) ^ 2)).add
      (hasSum_ite_eq r ((-2 / Real.pi) ^ 2))).add hBs.hasSum
    have hs' : HasSum (fun x => b x ^ 2) ((2 / Real.pi) ^ 2 + (-2 / Real.pi) ^ 2 + B) := by
      apply hs.congr_fun
      intro x
      by_cases hxl : x = l
      · subst x; simp [hl, hlr, hbl]
      by_cases hxr : x = r
      · subst x; simp [hr, Ne.symm hlr, hbr]
      by_cases hxS : x ∈ S
      · simp [hxl, hxr, hxS]
      · simp [hxl, hxr, hxS, hsupport x hxl hxr hxS]
    exact hs'.unique hb
  have hC : a l * (2 / Real.pi) + (-a l) * (-2 / Real.pi) + C = 0 := by
    have hs := ((hasSum_ite_eq l (a l * (2 / Real.pi))).add
      (hasSum_ite_eq r ((-a l) * (-2 / Real.pi)))).add hCs.hasSum
    have hs' : HasSum (fun x => a x * b x)
        (a l * (2 / Real.pi) + (-a l) * (-2 / Real.pi) + C) := by
      apply hs.congr_fun
      intro x
      by_cases hxl : x = l
      · subst x; simp [hl, hlr, hbl]
      by_cases hxr : x = r
      · subst x; simp [hr, Ne.symm hlr, har, hbr]
      by_cases hxS : x ∈ S
      · simp [hxl, hxr, hxS]
      · simp [hxl, hxr, hxS, hsupport x hxl hxr hxS]
    exact hs'.unique hab
  have hsquare : HasSum (S.indicator (fun x => (a x + (Real.pi * a l) * b x) ^ 2))
      (A + (2 * Real.pi * a l) * C + (Real.pi * a l) ^ 2 * B) := by
    have hs := (hAs.hasSum.add (hCs.hasSum.mul_left (2 * Real.pi * a l))).add
      (hBs.hasSum.mul_left ((Real.pi * a l) ^ 2))
    apply hs.congr_fun
    intro x
    by_cases hx : x ∈ S <;> simp only [Set.indicator_apply, hx, ite_true, ite_false] <;> ring
  have hnonneg : 0 ≤ A + (2 * Real.pi * a l) * C + (Real.pi * a l) ^ 2 * B :=
    hasSum_le (fun x => Set.indicator_nonneg (fun _ _ => sq_nonneg _) x) hasSum_zero hsquare
  have hC' : Real.pi * C = -4 * a l := by
    have h := congrArg (fun t : ℝ => Real.pi * t) hC
    field_simp at h
    linarith only [h]
  have hB' : Real.pi ^ 2 * B = Real.pi ^ 2 - 8 := by
    have h := congrArg (fun t : ℝ => Real.pi ^ 2 * t) hB
    field_simp at h
    linarith only [h]
  have heq : (2 * Real.pi * a l) * C + (Real.pi * a l) ^ 2 * B =
      (Real.pi ^ 2 - 16) * a l ^ 2 := by
    calc
      _ = 2 * a l * (Real.pi * C) + a l ^ 2 * (Real.pi ^ 2 * B) := by ring
      _ = _ := by rw [hC', hB']; ring
  rw [add_assoc, heq] at hnonneg
  dsimp only [A] at hnonneg ⊢
  nlinarith [mul_nonneg (sub_nonneg.mpr residual_pi_sq_le_ten) (sq_nonneg (a l))]

end ASDExplicitGamma.Cold
