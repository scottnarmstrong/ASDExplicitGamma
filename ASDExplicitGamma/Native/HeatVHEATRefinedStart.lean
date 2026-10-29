module

public import ASDExplicitGamma.Native.HeatVHEATRefinedAssembly

/-! The source start of the actual depth-ten refined VHEAT carrier. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Numerics.Native
open scoped ENNReal

local instance nativeHeatQ3RefinedStartIndexNeZero :
    NeZero (3 ^ 10 * 3 ^ 10) := ⟨by norm_num⟩

local instance nativeHeatQ3RefinedStartChildCompact (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    CompactSpace (closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i))) :=
  isCompact_iff_compactSpace.mp
    (isBounded_cubeSet (nativeHeatQ3RefinedCarrierChild m i)).isCompact_closure

local instance nativeHeatQ3RefinedStartChildFinite (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    IsFiniteMeasure
      (volumeMeasureOn (cubeSet (nativeHeatQ3RefinedCarrierChild m i))) :=
  ((isBounded_cubeSet (nativeHeatQ3RefinedCarrierChild m i)).isBoundedDomain).isFiniteMeasure_restrict_volume

/-- The power test for the actual refined child traces at the fixed true frame. -/
noncomputable def nativeHeatQ3RefinedCarrierPowerTest
    (M : ABKModel 2) (m : ℤ) (k : ℕ) :
    (∀ i : nativeHeatQ3RefinedCarrierIndex,
      C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ)) → ℝ :=
  childPower
    (fun i : nativeHeatQ3RefinedCarrierIndex =>
      cubeSet (nativeHeatQ3RefinedCarrierChild m i))
    (fun i => measurableSet_cubeSet (nativeHeatQ3RefinedCarrierChild m i))
    (fun i => volume_cubeSet_toReal_pos (nativeHeatQ3RefinedCarrierChild m i))
    M.nu (Annealed.sigmaBar M (m + 1) : ℝ) M.nu_pos
    (Annealed.sigmaBar_characterization M (m + 1)).1 k

end ASDExplicitGamma.Native

end
