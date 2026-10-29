module
public import ASDExplicitGamma.Numerics.Native.PanelMonotone
public import Mathlib.Data.List.GetD

/-! OLD boundary-fixed panel formula. Input order is
v, A2, kappa, kd, op, om, betaPlus, betaMinus, x, y, delta,
meanslope, xislope, H0, a0, xi0, ybar, time.
All general D factors remain 1+3^(-1/4). Only the boundary charge is corrected.
-/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open ASDExplicitGamma.Numerics ASDExplicitGamma.Numerics.Mirror

def nativePanelOps : List Expr := [
  .const (2/1 : ℚ),
  .sqrt (.var 0),
  .const (3/1 : ℚ),
  .sqrt (.var 0),
  .sqrt (.var 0),
  .const (105/1 : ℚ),
  .sqrt (.var 0),
  .sqrt (.var 0),
  .sqrt (.var 0),
  .const (1/1 : ℚ),
  .divPos (.var 0) (.var 5),
  .add (.var 0) (.var 1),
  .mul (.var 19) (.var 12),
  .add (.var 17) (.var 0),
  .sqrt (.var 0),
  .mul (.var 32) (.var 14),
  .mul (.var 0) (.var 16),
  .sqrt (.var 0),
  .const (3683/2500 : ℚ),
  .sqrt (.var 0),
  .mul (.var 15) (.var 0),
  .const (3/10000000000000000000000000000000000000000000000 : ℚ),
  .sqrt (.var 0),
  .mul (.var 14) (.var 0),
  .add (.var 3) (.var 0),
  .mul (.var 7) (.var 0),
  .add (.var 11) (.var 0),
  .mul (.var 17) (.var 0),
  .mul (.var 0) (.var 1),
  .mul (.var 35) (.var 29),
  .add (.var 33) (.var 0),
  .mul (.var 36) (.var 31),
  .add (.var 34) (.var 0),
  .sqrt (.var 0),
  .mul (.var 5) (.var 33),
  .add (.var 0) (.var 25),
  .sqrt (.var 1),
  .add (.var 1) (.var 0),
  .mul (.var 26) (.var 0),
  .mul (.var 0) (.var 10),
  .sqrt (.var 0),
  .mul (.var 3) (.var 22),
  .sqrt (.var 0),
  .add (.var 0) (.var 33),
  .mul (.var 34) (.var 57),
  .mul (.var 0) (.var 58),
  .const (38229489/6250000 : ℚ),
  .mul (.var 1) (.var 0),
  .mul (.var 38) (.var 5),
  .mul (.var 0) (.var 6),
  .mul (.var 40) (.var 62),
  .mul (.var 0) (.var 63),
  .mul (.var 2) (.var 0),
  .add (.var 5) (.var 0),
  .sqrt (.var 0),
  .mul (.var 53) (.var 21),
  .mul (.var 0) (.var 65),
  .mul (.var 0) (.var 70),
  .mul (.var 56) (.var 57),
  .mul (.var 0) (.var 18),
  .mul (.var 0) (.var 68),
  .mul (.var 0) (.var 73),
  .add (.var 4) (.var 0),
  .mul (.var 17) (.var 44),
  .add (.var 1) (.var 0),
  .mul (.var 27) (.var 13),
  .add (.var 1) (.var 0),
  .mul (.var 81) (.var 66),
  .mul (.var 34) (.var 76),
  .mul (.var 67) (.var 25),
  .mul (.var 0) (.var 82),
  .add (.var 2) (.var 0),
  .mul (.var 4) (.var 0),
  .add (.var 6) (.var 0),
  .mul (.var 64) (.var 89),
  .mul (.var 0) (.var 90),
  .mul (.var 0) (.var 57),
  .mul (.var 92) (.var 76),
  .mul (.var 0) (.var 44),
  .sqrt (.var 96),
  .mul (.var 1) (.var 0),
  .mul (.var 3) (.var 26),
  .add (.var 1) (.var 0),
  .mul (.var 15) (.var 71),
  .mul (.var 0) (.var 99),
  .mul (.var 0) (.var 66),
  .mul (.var 0) (.var 84),
  .add (.var 4) (.var 0),
  .add (.var 97) (.var 96),
  .mul (.var 55) (.var 0),
  .divPos (.var 0) (.var 88),
  .mul (.var 79) (.var 72),
  .mul (.var 0) (.var 105),
  .add (.var 2) (.var 0),
  .mul (.var 50) (.var 106),
  .add (.var 1) (.var 0),
  .mul (.var 28) (.var 0),
  .mul (.var 20) (.var 64),
  .add (.var 24) (.var 0),
  .mul (.var 11) (.var 65),
  .add (.var 1) (.var 0),
  .mul (.var 4) (.var 99),
  .mul (.var 0) (.var 68),
  .add (.var 2) (.var 0),
  .mul (.var 18) (.var 71),
  .add (.var 1) (.var 0),
  .mul (.var 117) (.var 105),
  .mul (.var 0) (.var 73),
  .add (.var 2) (.var 0),
  .mul (.var 119) (.var 108),
  .mul (.var 0) (.var 108),
  .mul (.var 0) (.var 77),
  .add (.var 3) (.var 0),
  .divPos (.var 114) (.var 112),
  .mul (.var 0) (.var 83),
  .const (1183/2500 : ℚ),
  .mul (.var 100) (.var 0),
  .add (.var 2) (.var 0),
  .const (4/1 : ℚ),
  .add (.var 60) (.var 0),
  .const (156/5 : ℚ),
  .mul (.var 1) (.var 0),
  .mul (.var 0) (.var 138),
  .const (9/1 : ℚ),
  .divPos (.var 1) (.var 0),
  .add (.var 7) (.var 0),
  .add (.var 0) (.var 13)
]

noncomputable def nativePanelValue (fields : List ℝ) (s : ℝ) : ℝ :=
  (nativePlanReal (s::fields.reverse) nativePanelOps).getD 0 0

def nativePanelInputs (fields : List QInterval) (s : ℚ) : List QInterval :=
  gridConstant 60 s::fields.reverse

theorem nativePanelInputs_sound (fieldsI : List QInterval) (fieldsR : List ℝ) (s : ℚ)
    (hf : ∀ i, QInterval.Contains (fieldsI.getD i nativeZeroInterval) (fieldsR.getD i 0))
    (hlen : fieldsI.length = fieldsR.length) :
    ∀ i, QInterval.Contains ((nativePanelInputs fieldsI s).getD i nativeZeroInterval)
      (((s : ℝ)::fieldsR.reverse).getD i 0) := by
  intro i
  cases i with
  | zero => exact gridConstant_sound 60 s
  | succ i =>
    change QInterval.Contains (fieldsI.reverse.getD i nativeZeroInterval) (fieldsR.reverse.getD i 0)
    by_cases hi : i < fieldsI.length
    · rw [List.getD_reverse i hi,List.getD_reverse i (by simpa [← hlen] using hi)]
      simpa only [← hlen] using hf (fieldsI.length-1-i)
    · have hiR : fieldsR.length ≤ i := by omega
      rw [List.getD_eq_default fieldsI.reverse nativeZeroInterval (by simpa using Nat.le_of_not_gt hi),List.getD_eq_default fieldsR.reverse 0 (by simpa using hiR)]
      norm_num [nativeZeroInterval,QInterval.Contains]

theorem nativeList_getD_nonneg (xs : List ℝ) (h : ∀ x ∈ xs, 0 ≤ x) (i : ℕ) :
    0 ≤ xs.getD i 0 := by
  induction xs generalizing i with
  | nil => simp
  | cons x xs ih =>
    cases i with
    | zero => exact h x (by simp)
    | succ i => exact ih (fun y hy => h y (by simp only [List.mem_cons]; exact Or.inr hy)) i

theorem nativePanel_positive_checked : nativePlanPositiveCheck 17 nativePanelOps = true := by
  decide +kernel

/-- Analytic monotonicity on the full nonnegative time axis, including every panel interior. -/
theorem nativePanel_monotone (fields : List ℝ) (hlen : fields.length = 17)
    (hfields : ∀ x ∈ fields, 0 ≤ x) : MonotoneOn (nativePanelValue fields) (Set.Ici 0) := by
  apply nativePlanPositiveCheck_sound fields.length nativePanelOps (fun s => s::fields.reverse)
  · intro i
    cases i with
    | zero =>
      constructor
      · intro s hs; exact hs
      · intro s hs t ht hst; exact hst
      · intro h; contradiction
    | succ i =>
      simp only [List.getD_eq_getElem?_getD]
      constructor
      · intro s hs
        exact nativeList_getD_nonneg fields.reverse (by simpa only [List.mem_reverse] using hfields) i
      · intro s hs t ht hst; exact le_rfl
      · intro h s t; rfl
  · rw [hlen]
    exact nativePanel_positive_checked

end ASDExplicitGamma.Numerics.Native
