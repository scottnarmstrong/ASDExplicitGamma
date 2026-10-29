module

public import ASDExplicitGamma.Native.HeatStepDefs

/-! Numerical certificates of the 48-pass refined-child heat recursion for `ns` shells:
nonnegativity of the configured rows, the exponential check, the generalized-Holder root
certificates of the top degree, and the checked roots consumed by every one of the 48 passes.
The certificates are computed by a Boolean checker (`nativeHeatStepPassCheck`) that is
evaluated in the kernel once per `ns` in the generated `HeatStepPassDataGen*` modules. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native

/-- Checked roots for the first `n` passes started from `y`. -/
def nativeHeatPassRootsOk (old : NativeOldRow) (frames : NativeHeatFrameInputs)
    (coef fixed : List ℚ) (base : ℚ) : ℕ → ℚ → Bool
  | 0, _ => true
  | n + 1, y =>
    nativeRootValid (heatPassMomentBudget old frames coef fixed base y) 20 &&
      nativeHeatPassRootsOk old frames coef fixed base n
        (nativeHeatPass old frames coef fixed base y)

theorem nativeHeatPassRootsOk_sound (old : NativeOldRow) (frames : NativeHeatFrameInputs)
    (coef fixed : List ℚ) (base : ℚ) (n : ℕ) :
    ∀ y : ℚ, nativeHeatPassRootsOk old frames coef fixed base n y = true →
      ∀ i < n, nativeRootValid
        (heatPassMomentBudget old frames coef fixed base
          (nativeHeatPasses old frames coef fixed base i y)) 20 = true := by
  induction n with
  | zero => intro y _ i hi; omega
  | succ n ih =>
    intro y hy i hi
    simp only [nativeHeatPassRootsOk, Bool.and_eq_true] at hy
    cases i with
    | zero => simpa [nativeHeatPasses] using hy.1
    | succ j =>
      have := ih _ hy.2 j (by omega)
      simpa [nativeHeatPasses] using this

/-- The Boolean pass certificate for `ns` shells. -/
def nativeHeatStepPassCheck (ns : ℕ) : Bool :=
  let old := nativeHeatOldRowGen ns
  let fr := nativeHeatFramesGen ns
  let fixed := nativeHeatFixedGen ns
  let init := nativeHeatInitGen ns
  decide (0 ≤ old.e) && decide (0 ≤ nativeHeatExpArgGen ns) &&
  nativeHeatExpCheck (nativeHeatExpArgGen ns) (nativeHeatExpGen ns) &&
  decide (0 < fr.x) && decide (0 ≤ fr.y) && decide (0 ≤ fr.raw) &&
  nativeRootValid ((fr.raw / fr.x) ^ 5) 27 && nativeRootValid ((fr.raw / fr.x) ^ 10) 27 &&
  (List.range 20).all (fun j => decide (0 ≤ fixed.getD j 0)) &&
  (List.range 21).all (fun j => decide (0 ≤ init.getD j 0)) &&
  nativeHeatPassRootsOk old fr (nativeHeatCoefGen ns) fixed (nativeHeatBaseGen ns) 48 fr.y

/-- The numerical certificates for the 48-pass recursion at `ns` shells. -/
structure NativeHeatStepPassNum (ns : ℕ) : Prop where
  old_e_nonneg : 0 ≤ (nativeHeatOldRowGen ns).e
  c_nonneg : 0 ≤ nativeHeatExpArgGen ns
  exp_check : nativeHeatExpCheck (nativeHeatExpArgGen ns) (nativeHeatExpGen ns) = true
  x_pos : 0 < (nativeHeatFramesGen ns).x
  y_nonneg : 0 ≤ (nativeHeatFramesGen ns).y
  raw_nonneg : 0 ≤ (nativeHeatFramesGen ns).raw
  root5 : nativeRootValid (((nativeHeatFramesGen ns).raw / (nativeHeatFramesGen ns).x) ^ 5) 27 = true
  root10 : nativeRootValid (((nativeHeatFramesGen ns).raw / (nativeHeatFramesGen ns).x) ^ 10) 27 = true
  fixed_nonneg : ∀ j < 20, 0 ≤ (nativeHeatFixedGen ns).getD j 0
  init_nonneg : ∀ j ≤ 20, 0 ≤ (nativeHeatInitGen ns).getD j 0
  pass_roots : ∀ i < 48, nativeRootValid
    (heatPassMomentBudget (nativeHeatOldRowGen ns) (nativeHeatFramesGen ns)
      (nativeHeatCoefGen ns) (nativeHeatFixedGen ns) (nativeHeatBaseGen ns)
      (nativeHeatPasses (nativeHeatOldRowGen ns) (nativeHeatFramesGen ns)
        (nativeHeatCoefGen ns) (nativeHeatFixedGen ns) (nativeHeatBaseGen ns) i
        (nativeHeatFramesGen ns).y)) 20 = true

theorem nativeHeatStepPassNum_of_check (ns : ℕ)
    (h : nativeHeatStepPassCheck ns = true) : NativeHeatStepPassNum ns := by
  unfold nativeHeatStepPassCheck at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, ?_, ?_, ?_⟩
  · intro j hj; exact h9 j hj
  · intro j hj; exact h10 j (by omega)
  · exact nativeHeatPassRootsOk_sound _ _ _ _ _ 48 _ h11

end ASDExplicitGamma.Native

end
