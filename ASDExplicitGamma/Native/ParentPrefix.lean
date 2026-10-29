module

public import ASDExplicitGamma.Native.SmallerGamma
public import ASDExplicitGamma.Native.SmallerGammaWeak

/-! The actual-law boundary-fixed parent rows and their completed-prefix
endpoint caps, ready to instantiate from the producer conclusions. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Numerics.Native
open scoped ENNReal
noncomputable section

/-- Exact source conclusion of NA-PARENT-PREFIX in the completed true frame. -/
def NativeParentPrefixConclusion
    (M : ABKModel 2) (m : ℤ) : Prop :=
  (∀ j : Fin 16, nativeCompletedSourceMean M m (j.val+1) ≤
    ENNReal.ofReal
      (theta M * ((nativeBoundaryParentCaps.getD (j.val+1) 0 : ℚ) : ℝ))) ∧
  (∀ r : Fin 6, nativeCompletedSourceMean M m r.val ≤
    ENNReal.ofReal
      (theta M * ((nativeCompletedMeanRows.getD r.val 0 : ℚ) : ℝ))) ∧
  (∀ r : Fin 6, nativeCompletedSourceWeak M m r.val ≤
    ENNReal.ofReal
      (theta M * ((nativeCompletedWeakRows.getD r.val 0 : ℚ) : ℝ)) )

/-- Preserve the source-smaller-γ predecessor and assemble NA-PARENT-PREFIX
from the exact parent-boundary and completed-prefix producer conclusions. -/
theorem native_parent_prefix_bundle_of_producers
    (M : ABKModel 2) (m : ℤ)
    (hsource : NativeSourceSmallerGammaBounds M m)
    (hparent : ∀ j : Fin 16, nativeCompletedSourceMean M m (j.val+1) ≤
      ENNReal.ofReal
        (theta M * ((nativeBoundaryParentCaps.getD (j.val+1) 0 : ℚ) : ℝ)))
    (hprefix :
      (∀ r : Fin 6, nativeCompletedSourceMean M m r.val ≤
        ENNReal.ofReal
          (theta M * ((nativeCompletedMeanRows.getD r.val 0 : ℚ) : ℝ))) ∧
      (∀ r : Fin 6, nativeCompletedSourceWeak M m r.val ≤
        ENNReal.ofReal
          (theta M * ((nativeCompletedWeakRows.getD r.val 0 : ℚ) : ℝ)))) :
    NativeSourceSmallerGammaBounds M m ∧ NativeParentPrefixConclusion M m := by
  exact ⟨hsource, ⟨hparent, hprefix.1, hprefix.2⟩⟩

/-- Parent-prefix bounds from the exact predecessor and producer
conclusions. The positive-prefix calculation, including every retained tail
and rare term, is part of `hprefix`, not an assumed rounded cap. -/
theorem native_parent_prefix_of_producers
    (M : ABKModel 2) (m : ℤ)
    (hsource : NativeSourceSmallerGammaBounds M m)
    (hparent : ∀ j : Fin 16, nativeCompletedSourceMean M m (j.val+1) ≤
      ENNReal.ofReal
        (theta M * ((nativeBoundaryParentCaps.getD (j.val+1) 0 : ℚ) : ℝ)))
    (hprefix :
      (∀ r : Fin 6, nativeCompletedSourceMean M m r.val ≤
        ENNReal.ofReal
          (theta M * ((nativeCompletedMeanRows.getD r.val 0 : ℚ) : ℝ))) ∧
      (∀ r : Fin 6, nativeCompletedSourceWeak M m r.val ≤
        ENNReal.ofReal
          (theta M * ((nativeCompletedWeakRows.getD r.val 0 : ℚ) : ℝ)))) :
    NativeParentPrefixConclusion M m :=
  (native_parent_prefix_bundle_of_producers M m hsource hparent hprefix).2

private theorem configuredParent_cap_eq (j : Fin 16) :
    (nativeConfiguredParentEndpoint j).cap = nativeBoundaryParentCaps.getD (j.val+1) 0 := by
  fin_cases j <;> rfl

/-- Each boundary-fixed actual parent bound implies the legacy carried
parent enclosure by the exact endpoint certificate's strict comparison. -/
theorem native_parent_prefix_carried
    (M : ABKModel 2) (m : ℤ) (hsource : NativeSourceSmallerGammaBounds M m)
    (j : Fin 16) : nativeCompletedSourceMean M m (j.val+1) ≤
      ENNReal.ofReal (theta M * ((nativeConfiguredParentEndpoint j).carried : ℝ)) := by
  have ht : 0 ≤ theta M := div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  have hc : ((nativeBoundaryParentCaps.getD (j.val+1) 0 : ℚ) : ℝ) ≤
      ((nativeConfiguredParentEndpoint j).carried : ℝ) := by
    rw [← configuredParent_cap_eq j]
    exact_mod_cast (native_boundary_parent_endpoint_carried j).le
  exact (hsource.parent j).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hc ht))

/-- The actual boundary-fixed depth-14 mean is below the separately retained
upper safe cap. This is a comparator for the actual mean, not an assertion
identifying the boundary-fixed return with the plain-old return formula. -/
theorem native_parent_prefix_fourteen_safe
    (M : ABKModel 2) (m : ℤ) (hsource : NativeSourceSmallerGammaBounds M m) :
    nativeCompletedSourceMean M m 14 ≤ ENNReal.ofReal
      (theta M * (13276004954337698463246677797499/10^32 : ℝ)) := by
  have ht : 0 ≤ theta M := div_nonneg M.shellPrefix.gamma_pos.le (by norm_num [gammaZero])
  have hc : (nativeBoundaryParentCaps.getD 14 0 : ℚ) ≤
      13276004954337698463246677797499/10^32 := by decide +kernel
  have hcR : ((nativeBoundaryParentCaps.getD 14 0 : ℚ) : ℝ) ≤
      (13276004954337698463246677797499/10^32 : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr hc
  exact (hsource.parent (13 : Fin 16)).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hcR ht))

end
end ASDExplicitGamma.Native
