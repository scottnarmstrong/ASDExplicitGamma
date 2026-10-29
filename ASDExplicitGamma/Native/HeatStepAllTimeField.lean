module

public import ASDExplicitGamma.Native.HeatStepWeightedIndividual
public import ASDExplicitGamma.Native.ParentBoundaryObserverBandHeat
public import ASDExplicitGamma.Native.GenericSourceEndpoints

/-! The weighted band with amplitude `1` on the shell `q+1` and `√t` on the further shells is the
heat-path field `olderField_{q+1} + √t · (shells q+2, …, q+ns+1)`. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open Homogenization Algsuperdiff.Section3 MeasureTheory ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic

/-- Amplitude `1` on the shell `q + 1` and `√t` on every other shell. -/
noncomputable def nativeHeatStepAmp (q : ℤ) (t : ℝ) (ht1 : t ≤ 1) : NativeAmp where
  w := fun j => if j = q + 1 then 1 else Real.sqrt t
  nonneg := fun j => by
    by_cases h : j = q + 1
    · simp [h]
    · simp [h, Real.sqrt_nonneg]
  le_one := fun j => by
    by_cases h : j = q + 1
    · simp [h]
    · simpa [h] using Real.sqrt_le_one.mpr ht1

theorem nativeHeatStep_weightedBand_eq (q : ℤ) (ns : ℕ) (t : ℝ) (ht1 : t ≤ 1)
    (ω : Cutoff.CutoffSample 2) :
    nativeSourceBandScalar_W (nativeHeatStepAmp q t ht1) q (ns + 1) 1 ω =
      parentBoundaryObserverBandScalar q (q + 1) ns t ω := by
  let K := closure (cubeSet (originCube 2 q))
  obtain ⟨ell, hK⟩ := exists_originCube_containing_compact K
    (isBounded_cubeSet (originCube 2 q)).isCompact_closure
  unfold nativeSourceBandScalar_W parentBoundaryObserverBandScalar modelBandW modelBand
  rw [native_source_older_field_succ K ell q hK ω, Fin.sum_univ_succ, Real.sqrt_one, one_smul]
  have h0 : nativeSourceBandCoef_W (nativeHeatStepAmp q t ht1) q (ns + 1) 0 = 1 := by
    simp [nativeSourceBandCoef_W, nativeHeatStepAmp, nativeSourceBandIndex]
  have hs : ∀ i : Fin ns, nativeSourceBandCoef_W (nativeHeatStepAmp q t ht1) q (ns + 1)
      i.succ = Real.sqrt t := by
    intro i
    simp only [nativeSourceBandCoef_W, nativeHeatStepAmp, nativeSourceBandIndex,
      Fin.val_succ]
    rw [if_neg]
    push_cast
    omega
  have hi : ∀ i : Fin ns, nativeSourceBandIndex q (ns + 1) i.succ =
      nativeSourceBandIndex (q + 1) ns i := by
    intro i
    simp only [nativeSourceBandIndex, Fin.val_succ]; push_cast; ring
  simp only [h0, hs, hi, one_smul, ← Finset.smul_sum, smul_add]
  have e : nativeSourceBandIndex q (ns + 1) 0 = q + 1 := by simp [nativeSourceBandIndex]
  rw [e, add_assoc]

end ASDExplicitGamma.Native
