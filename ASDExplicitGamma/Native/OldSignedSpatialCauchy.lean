module

public import ASDExplicitGamma.Native.OldSignedDescendantMinkowski

/-! Cauchy--Schwarz under the actual finite descendant averages. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization
noncomputable section

/-- Joint spatial contraction without replacing cell averages by maxima. -/
theorem old_signed_descendant_cauchy (Q : TriadicCube 2) (r : ℕ)
    (f g : TriadicCube 2 → ℝ)
    (hf : ∀ U ∈ descendantsAtDepth Q r,0≤f U)
    (hg : ∀ U ∈ descendantsAtDepth Q r,0≤g U) :
    descendantsAverage Q r (fun U => f U*g U)≤
      Real.sqrt (descendantsAverage Q r (fun U => f U^2))*
        Real.sqrt (descendantsAverage Q r (fun U => g U^2)) := by
  have hh := descendantsAverage_mul_le_Lp_mul_Lq_of_nonneg Q r f g
    (show Real.HolderConjugate 2 2 from Real.holderConjugate_iff.mpr (by norm_num)) hf hg
  simpa only [Real.rpow_ofNat,←Real.sqrt_eq_rpow] using hh

end
end ASDExplicitGamma.Native
