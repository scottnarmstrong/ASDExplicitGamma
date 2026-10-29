module
public import ASDExplicitGamma.Numerics.Native.History
public import Mathlib.Data.List.GetD

/-! Soundness of the complete outward finite-history recurrence against the source real frames
and the exact geometric history clock. -/
@[expose] public section
namespace ASDExplicitGamma.Numerics.Native

noncomputable def nativeHistoryReal (offset start : ℕ) : List ℚ → ℝ
  | [] => 0
  | t::ts =>
      (nativeC0 : ℝ)*(nativeHistoryRatio : ℝ)^start*
        nativeFrameReal (((11/10)*(2*nativeGamma*(offset+start : ℕ)) : ℚ) : ℝ) (t : ℝ)+
      nativeHistoryReal offset (start+1) ts

theorem nativeHistoryReal_append (offset start : ℕ) (xs ys : List ℚ) :
    nativeHistoryReal offset start (xs++ys) =
      nativeHistoryReal offset start xs+nativeHistoryReal offset (start+xs.length) ys := by
  induction xs generalizing start with
  | nil => simp only [List.nil_append,nativeHistoryReal,List.length_nil,Nat.add_zero,zero_add]
  | cons t ts ih =>
    simp only [List.cons_append,nativeHistoryReal,List.length_cons,ih]
    have he : start+1+ts.length = start+(ts.length+1) := by omega
    rw [he,add_assoc]

theorem nativeFrameReal_nonneg (a t : ℝ) (ha0 : 0 ≤ a) (ha1 : a < 1) (ht : 0 ≤ t) :
    0 ≤ nativeFrameReal a t := by
  rw [nativeFrameReal_formula a t ha1]
  have hq := nativeFrameQuadratic_nonneg a ha1
  positivity

/-- A checked block bounds every exact-weight real frame term, including all intermediate depths. -/
theorem nativeHistorySteps_sound (offset start : ℕ) (xs : List ℚ) (state : ℚ × ℚ)
    (ht : ∀ t ∈ xs, 0 ≤ t)
    (hd : ∀ i, i < xs.length →
      0 ≤ (11/10)*(2*nativeGamma*(offset+start+i : ℕ)) ∧
      (11/10)*(2*nativeGamma*(offset+start+i : ℕ)) < 1)
    (hr : ∀ i, i < xs.length → nativeRootValid ((xs.getD i 0)*(xs.getD i 0+8)) 2 = true)
    (hw : (nativeHistoryRatio : ℝ)^start ≤ (state.1 : ℝ)) :
    nativeHistoryReal offset start xs ≤
      ((nativeHistorySteps offset start xs.length xs state).2 : ℝ)-(state.2 : ℝ) := by
  have hQ : (0 : ℝ) ≤ nativeHistoryRatio := by
    exact_mod_cast (show (0 : ℚ) ≤ nativeHistoryRatio by decide +kernel)
  have hC : (0 : ℝ) ≤ nativeC0 := by
    exact_mod_cast (show (0 : ℚ) ≤ nativeC0 by decide +kernel)
  induction xs generalizing start state with
  | nil => simp only [nativeHistoryReal,List.length_nil,nativeHistorySteps,sub_self,le_refl]
  | cons t ts ih =>
    have hd0 := hd 0 (by simp)
    have hr0 := hr 0 (by simp)
    have hf := nativeShiftedFrame_sound (offset+start) t hd0 hr0
    have htn : (0 : ℝ) ≤ t := by exact_mod_cast ht t (by simp)
    have hfn : 0 ≤ nativeFrameReal (((11/10)*(2*nativeGamma*(offset+start : ℕ)) : ℚ) : ℝ) (t : ℝ) :=
      nativeFrameReal_nonneg _ _ (by exact_mod_cast hd0.1) (by exact_mod_cast hd0.2) htn
    have hp : (0 : ℝ) ≤ state.1 := (pow_nonneg hQ start).trans hw
    have hterm := mul_le_mul (mul_le_mul_of_nonneg_left hw hC) hf hfn (mul_nonneg hC hp)
    have hu := (Rat.cast_le (K := ℝ)).2
      (nativeUp_ge (nativeC0*state.1*nativeShiftedFrame (offset+start) t))
    have hterm' : (nativeC0 : ℝ)*(nativeHistoryRatio : ℝ)^start*
        nativeFrameReal (((11/10)*(2*nativeGamma*(offset+start : ℕ)) : ℚ) : ℝ) (t : ℝ) ≤
        (nativeUp (nativeC0*state.1*nativeShiftedFrame (offset+start) t) : ℝ) :=
      hterm.trans (by simpa only [Rat.cast_mul] using hu)
    let next : ℚ × ℚ :=
      (nativeUp (state.1*nativeHistoryRatio),
       state.2+nativeUp (nativeC0*state.1*nativeShiftedFrame (offset+start) t))
    have hw' : (nativeHistoryRatio : ℝ)^(start+1) ≤ (next.1 : ℝ) := by
      rw [pow_succ]
      apply (mul_le_mul_of_nonneg_right hw hQ).trans
      have h := (Rat.cast_le (K := ℝ)).2 (nativeUp_ge (state.1*nativeHistoryRatio))
      simpa only [Rat.cast_mul] using h
    have hd' (i : ℕ) (hi : i < ts.length) :
        0 ≤ (11/10)*(2*nativeGamma*(offset+(start+1)+i : ℕ)) ∧
        (11/10)*(2*nativeGamma*(offset+(start+1)+i : ℕ)) < 1 := by
      have h := hd (i+1) (by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using hi)
      have he : offset+start+(i+1) = offset+(start+1)+i := by omega
      simpa only [he] using h
    have hr' (i : ℕ) (hi : i < ts.length) :
        nativeRootValid ((ts.getD i 0)*(ts.getD i 0+8)) 2 = true := by
      simpa only [List.getD_cons_succ] using hr (i+1)
        (by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using hi)
    have hi := ih (start+1) next (fun u hu => ht u (by simp only [List.mem_cons]; exact Or.inr hu)) hd' hr' hw'
    simp only [nativeHistoryReal,List.length_cons,nativeHistorySteps]
    calc
      _ ≤ (nativeUp (nativeC0*state.1*nativeShiftedFrame (offset+start) t) : ℝ)+
          (((nativeHistorySteps offset (start+1) ts.length ts next).2 : ℝ)-(next.2 : ℝ)) :=
        add_le_add hterm' hi
      _ = _ := by
        dsimp only [next]
        push_cast
        ring

end ASDExplicitGamma.Numerics.Native
