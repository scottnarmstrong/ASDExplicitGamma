module

public import ASDExplicitGamma.Statements.NativeInductionState
import Lean.Elab.Tactic.Omega

/-! Root-relative protected reset labels and the exact earlier native coordinates.
No structural frame-continuity statement is used in this chronology. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Algsuperdiff.Section3

/-- Reset chronology: k+ceil(k/3)+H+3, with k starting at one. -/
def resetDepth (H k : ℕ) : ℤ := (k : ℤ)+((k+2)/3 : ℕ)+(H : ℤ)+3

theorem local_protected_gap (H k : ℕ) (hH : 377 ≤ H) (hk : 1 ≤ k) :
    (342 : ℤ) ≤ resetDepth H k-40 := by
  unfold resetDepth
  omega

theorem global_protected_gap (H k : ℕ) (hH : 333 ≤ H) (hk : 1 ≤ k) :
    (298 : ℤ) ≤ resetDepth H k-40 := by
  unfold resetDepth
  omega

/-- The full/local protected entrance, before any source-root substitution. -/
theorem local_reset_labels (N m l r b : ℤ) (hm : m < N) (hl : l ≤ m+40)
    (hr : 342 ≤ r-b) :
    l-r+b ≤ l-342 ∧ l-342 ≤ m-302 ∧ m-302 ≤ N-303 := by omega

/-- The distinct short-global protected entrance. -/
theorem global_reset_labels (N m l r b : ℤ) (hm : m < N) (hl : l ≤ m+40)
    (hr : 298 ≤ r-b) :
    l-r+b ≤ l-298 ∧ l-298 ≤ m-258 ∧ m-258 ≤ N-259 := by omega

/-- The first local cap of a one-pass root k=n-40 reads labels through n-382. -/
theorem one_pass_reset_labels (n r b : ℤ) (hr : 342 ≤ r-b) :
    n-40 < n ∧ (n-40)-r+b ≤ n-382 := by omega

/-- Project precisely the source reset coordinates from an earlier native state. -/
theorem reset_native_coordinates (M : ABKModel 2) (h : ℝ) (j : ℤ)
    (hj : nativeInductionState M h j) :
    buffer40History M j ≤ ENNReal.ofReal (61/10*theta M) ∧
    bufferMean M j ≤ ENNReal.ofReal (8/25*theta M) ∧
    M.nu ≤ (Annealed.sigmaBar M j : ℝ) ∧
    (31/50)*shellVarianceSum h M.gamma j+(19/50)*M.nu^2 ≤ (Annealed.sigmaBar M j : ℝ)^2 := by
  obtain ⟨_,_,_,hh,hm,hn,hl,_⟩ := hj
  exact ⟨hh,hm,hn,hl⟩

/-- The one-pass entry reads ordinary mean and the lower scalar at k=n-40. -/
theorem one_pass_native_coordinates (M : ABKModel 2) (h : ℝ) (n : ℤ)
    (hpast : ∀ j < n, nativeInductionState M h j) :
    ordinaryMean M (n-40) ≤ ENNReal.ofReal (3/50*theta M) ∧
    M.nu ≤ (Annealed.sigmaBar M (n-40) : ℝ) ∧
    (31/50)*shellVarianceSum h M.gamma (n-40)+(19/50)*M.nu^2 ≤
      (Annealed.sigmaBar M (n-40) : ℝ)^2 := by
  obtain ⟨ho,_,_,_,_,hn,hl,_⟩ := hpast (n-40) (by omega)
  exact ⟨ho,hn,hl⟩

/-- The full/local coordinates are genuinely earlier than the target N. -/
theorem local_reset_native_coordinates (M : ABKModel 2) (h : ℝ)
    (N m l r b : ℤ) (hm : m < N) (hl : l ≤ m+40) (hr : 342 ≤ r-b)
    (hpast : ∀ j < N, nativeInductionState M h j) :
    buffer40History M (l-r+b) ≤ ENNReal.ofReal (61/10*theta M) ∧
    bufferMean M (l-r+b) ≤ ENNReal.ofReal (8/25*theta M) ∧
    M.nu ≤ (Annealed.sigmaBar M (l-r+b) : ℝ) ∧
    (31/50)*shellVarianceSum h M.gamma (l-r+b)+(19/50)*M.nu^2 ≤
      (Annealed.sigmaBar M (l-r+b) : ℝ)^2 := by
  have hs := local_reset_labels N m l r b hm hl hr
  exact reset_native_coordinates M h _ (hpast _ (by omega))

/-- The global coordinates use the separate shorter protected range. -/
theorem global_reset_native_coordinates (M : ABKModel 2) (h : ℝ)
    (N m l r b : ℤ) (hm : m < N) (hl : l ≤ m+40) (hr : 298 ≤ r-b)
    (hpast : ∀ j < N, nativeInductionState M h j) :
    buffer40History M (l-r+b) ≤ ENNReal.ofReal (61/10*theta M) ∧
    bufferMean M (l-r+b) ≤ ENNReal.ofReal (8/25*theta M) ∧
    M.nu ≤ (Annealed.sigmaBar M (l-r+b) : ℝ) ∧
    (31/50)*shellVarianceSum h M.gamma (l-r+b)+(19/50)*M.nu^2 ≤
      (Annealed.sigmaBar M (l-r+b) : ℝ)^2 := by
  have hs := global_reset_labels N m l r b hm hl hr
  exact reset_native_coordinates M h _ (hpast _ (by omega))

/-- Source local/full resets, with their actual depth formula and b=40. -/
theorem local_reset_chronology (N m l : ℤ) (H k : ℕ) (hH : 377 ≤ H) (hk : 1 ≤ k)
    (hm : m < N) (hl : l ≤ m+40) :
    l-resetDepth H k+40 ≤ l-342 ∧ l-342 ≤ m-302 ∧ m-302 ≤ N-303 :=
  local_reset_labels N m l _ 40 hm hl (local_protected_gap H k hH hk)

/-- Source short-global resets, with their distinct H=333 depth. -/
theorem global_reset_chronology (N m l : ℤ) (H k : ℕ) (hH : 333 ≤ H) (hk : 1 ≤ k)
    (hm : m < N) (hl : l ≤ m+40) :
    l-resetDepth H k+40 ≤ l-298 ∧ l-298 ≤ m-258 ∧ m-258 ≤ N-259 :=
  global_reset_labels N m l _ 40 hm hl (global_protected_gap H k hH hk)

/-- The first local one-pass cap uses the same fixed protected entrance. -/
theorem one_pass_chronology (n : ℤ) (H k : ℕ) (hH : 377 ≤ H) (hk : 1 ≤ k) :
    n-40 < n ∧ (n-40)-resetDepth H k+40 ≤ n-382 :=
  one_pass_reset_labels n _ 40 (local_protected_gap H k hH hk)

end ASDExplicitGamma.Inverse
