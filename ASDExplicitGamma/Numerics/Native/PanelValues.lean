module
public import ASDExplicitGamma.Numerics.Native.PanelFormula

/-! Kernel-checkable panel blocks and their real pointwise soundness. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native
open ASDExplicitGamma.Numerics ASDExplicitGamma.Numerics.Mirror

theorem nativeSelect_sound (indices : List ℕ) (is : List QInterval) (rs : List ℝ)
    (hs : ∀ i, QInterval.Contains (is.getD i nativeZeroInterval) (rs.getD i 0)) :
    ∀ i, QInterval.Contains ((indices.map (fun j => is.getD j nativeZeroInterval)).getD i nativeZeroInterval)
      ((indices.map (fun j => rs.getD j 0)).getD i 0) := by
  intro i
  induction indices generalizing i with
  | nil => norm_num [nativeZeroInterval,QInterval.Contains]
  | cons j js ih =>
    cases i with
    | zero => exact hs j
    | succ i => exact ih i

theorem nativeFields_nonneg (is : List QInterval) (rs : List ℝ)
    (hs : ∀ i, QInterval.Contains (is.getD i nativeZeroInterval) (rs.getD i 0))
    (hl : ∀ i : Fin rs.length, 0 ≤ (is.getD i.val nativeZeroInterval).lo) :
    ∀ x ∈ rs, 0 ≤ x := by
  intro x hx
  obtain ⟨i,hi,hix⟩ := List.getElem_of_mem hx
  have h := ((Rat.cast_le (K := ℝ)).2 (hl ⟨i,hi⟩)).trans (hs i).1
  rw [List.getD_eq_getElem rs 0 hi,hix] at h
  simpa only [Rat.cast_zero] using h

theorem nativePanelUpper_sound (is : List QInterval) (rs : List ℝ) (s upper : ℚ)
    (hs : ∀ i, QInterval.Contains (is.getD i nativeZeroInterval) (rs.getD i 0))
    (hlen : is.length = rs.length)
    (hc : nativePlanUpperCheck (nativePanelInputs is s) nativePanelOps upper = true) :
    nativePanelValue rs (s : ℝ) ≤ (upper : ℝ) :=
  nativePlanUpperCheck_sound _ _ _ _ (nativePanelInputs_sound is rs s hs hlen) hc

def nativePanelChecks (inputs : List QInterval) (start : ℕ) : List ℚ → Bool
  | [] => true
  | upper::rest =>
    nativePlanUpperCheck (nativePanelInputs inputs ((start+1 : ℕ)/512)) nativePanelOps upper &&
      nativePanelChecks inputs (start+1) rest

theorem nativePanelChecks_append (inputs : List QInterval) (start : ℕ) (xs ys : List ℚ) :
    nativePanelChecks inputs start (xs++ys) =
      (nativePanelChecks inputs start xs && nativePanelChecks inputs (start+xs.length) ys) := by
  induction xs generalizing start with
  | nil => simp only [List.nil_append,nativePanelChecks,List.length_nil,Nat.add_zero,Bool.true_and]
  | cons x xs ih =>
    simp only [List.cons_append,nativePanelChecks,List.length_cons,ih]
    rw [Bool.and_assoc]
    have he : start+1+xs.length = start+(xs.length+1) := by omega
    rw [he]

theorem nativePanelChecks_sound (is : List QInterval) (rs : List ℝ)
    (hs : ∀ i, QInterval.Contains (is.getD i nativeZeroInterval) (rs.getD i 0))
    (hlen : is.length = rs.length) (start : ℕ) (caps : List ℚ)
    (hc : nativePanelChecks is start caps = true) :
    ∀ j, j < caps.length →
      nativePanelValue rs (((start+j+1 : ℕ)/512 : ℚ) : ℝ) ≤ (caps.getD j 0 : ℝ) := by
  induction caps generalizing start with
  | nil => intro j hj; simp only [List.length_nil,Nat.not_lt_zero] at hj
  | cons c cs ih =>
    rw [nativePanelChecks,Bool.and_eq_true] at hc
    intro j hj
    cases j with
    | zero => simpa only [Nat.add_zero,List.getD_cons_zero] using nativePanelUpper_sound is rs _ c hs hlen hc.1
    | succ j =>
      have hh := ih (start+1) hc.2 j (Nat.lt_of_succ_lt_succ hj)
      have he : start+(j+1)+1 = (start+1)+j+1 := by omega
      simpa only [he,List.getD_cons_succ] using hh

end ASDExplicitGamma.Numerics.Native
