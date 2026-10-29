module

public import ASDExplicitGamma.Model.Cutoff

/-! Amplitude vectors for the weighted simultaneous source band: shell `j` of the fresh band enters
with amplitude `√t · W j`, `W j ∈ [0,1]`. -/

@[expose] public section

namespace ASDExplicitGamma.Native

/-- Per-shell amplitude weights in `[0,1]`. -/
structure NativeAmp where
  w : ℤ → ℝ
  nonneg : ∀ j, 0 ≤ w j
  le_one : ∀ j, w j ≤ 1

/-- The shell attenuation vector of the weighted band at time `t`. -/
noncomputable def nativeAttW (W : NativeAmp) (t : ℝ) : ℤ → ℝ := fun j => Real.sqrt t * W.w j

theorem nativeAttW_mem (W : NativeAmp) {t : ℝ} (ht1 : t ≤ 1) (j : ℤ) :
    0 ≤ nativeAttW W t j ∧ nativeAttW W t j ≤ 1 := by
  refine ⟨mul_nonneg (Real.sqrt_nonneg t) (W.nonneg j), ?_⟩
  calc nativeAttW W t j = Real.sqrt t * W.w j := rfl
    _ ≤ 1 * 1 := mul_le_mul (Real.sqrt_le_one.mpr ht1) (W.le_one j) (W.nonneg j) zero_le_one
    _ = 1 := one_mul 1

/-- The uniform amplitude `1`. -/
def NativeAmp.one : NativeAmp := ⟨fun _ => 1, fun _ => zero_le_one, fun _ => le_rfl⟩


theorem NativeAmp.sq_le_one (W : NativeAmp) (j : ℤ) : W.w j ^ 2 ≤ 1 := by
  have h0 := W.nonneg j
  have h1 := W.le_one j
  nlinarith

/-- A signed row multiplied by a squared amplitude stays below a nonnegative majorant. -/
theorem nativeWeightedRow_le {a r c : ℝ} (ha : a ^ 2 ≤ 1) (hc : 0 ≤ c) (hr : r ≤ c) :
    a ^ 2 * r ≤ c := by
  have h2 : 0 ≤ a ^ 2 := sq_nonneg a
  nlinarith [mul_le_mul_of_nonneg_left hr h2]

end ASDExplicitGamma.Native
