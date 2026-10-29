module

public import ASDExplicitGamma.Native.HeatStepPassNum
public import ASDExplicitGamma.Native.HeatStepFrameNum
public import ASDExplicitGamma.Native.HeatStepIndivNum

/-! Helper lemmas for the per-`ns` generated numerics of the heat step: the literal-data
form of the pass certificate, and the assembly of the uniform structures from literals. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native

/-- The pass certificate for explicitly given (literal) data. -/
def nativeHeatStepPassCheckLit (old : NativeOldRow) (fr : NativeHeatFrameInputs)
    (c e : ℚ) (coef fixed init : List ℚ) (base : ℚ) : Bool :=
  decide (0 ≤ old.e) && decide (0 ≤ c) && nativeHeatExpCheck c e &&
  decide (0 < fr.x) && decide (0 ≤ fr.y) && decide (0 ≤ fr.raw) &&
  nativeRootValid ((fr.raw / fr.x) ^ 5) 27 && nativeRootValid ((fr.raw / fr.x) ^ 10) 27 &&
  (List.range 20).all (fun j => decide (0 ≤ fixed.getD j 0)) &&
  (List.range 21).all (fun j => decide (0 ≤ init.getD j 0)) &&
  nativeHeatPassRootsOk old fr coef fixed base 48 fr.y

theorem nativeHeatStep_list_ext_getD (l₁ l₂ : List ℚ) (hlen : l₁.length = l₂.length)
    (h : ∀ i < l₁.length, l₁.getD i 0 = l₂.getD i 0) : l₁ = l₂ := by
  apply List.ext_getElem hlen
  intro i hi₁ hi₂
  have := h i hi₁
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi₁, List.getElem?_eq_getElem hi₂]
    using this

theorem nativeHeatStep_map_range_getD (f : ℕ → ℚ) (n i : ℕ) (hi : i < n) :
    ((List.range n).map f).getD i 0 = f i := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem nativeHeatStepPassNum_of_literals (ns : ℕ) (old : NativeOldRow)
    (fr : NativeHeatFrameInputs) (c e : ℚ) (coef fixed init : List ℚ) (base : ℚ)
    (hOld : nativeHeatOldRowGen ns = old) (hFr : nativeHeatFramesGen ns = fr)
    (hc : nativeHeatExpArgGen ns = c) (he : nativeHeatExpGen ns = e)
    (hcoef : nativeHeatCoefGen ns = coef) (hfixed : nativeHeatFixedGen ns = fixed)
    (hinit : nativeHeatInitGen ns = init) (hbase : nativeHeatBaseGen ns = base)
    (hchk : nativeHeatStepPassCheckLit old fr c e coef fixed init base = true) :
    NativeHeatStepPassNum ns := by
  apply nativeHeatStepPassNum_of_check
  unfold nativeHeatStepPassCheck
  simp only [hOld, hFr, hc, he, hcoef, hfixed, hinit, hbase]
  exact hchk

end ASDExplicitGamma.Native

end
