module

public import ASDExplicitGamma.Native.GenericSourceBandPowerHeatW

public import ASDExplicitGamma.Native.NativeBandWeight

/-! Initial coordinates for the simultaneous actual source-band heat path. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Variational
open scoped ENNReal
noncomputable section

variable {W : NativeAmp}

/-- At time zero the simultaneous twentieth root is the completed source
root, including the same fixed true frame and unmodified coefficient law. -/
theorem native_source_band_p20_root_zero_W (M : ABKModel 2) (n : ℤ) (height : ℕ) :
    nativeSourceBandAverage_W W M n height
      (fun x => modelTraceObservable n M.nu (Annealed.sigmaBar M n) x^(20:ℝ)) 0^((20:ℝ)⁻¹) =
      nativeSourceBandRoot M n 0 := by
  unfold nativeSourceBandAverage_W nativeSourceBandScalar_W nativeSourceBandRoot
  simp only [Real.sqrt_zero,zero_smul,add_zero,Nat.cast_zero]

end
end ASDExplicitGamma.Native
