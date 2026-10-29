module

public import ASDExplicitGamma.Native.OldSignedProjectedStrongDerivative
public import ASDExplicitGamma.Native.OldSignedPhysicalPotential
public import ASDExplicitGamma.Native.OldSignedProjectedEnergy

/-! Spatial derivatives of actual projected white kernels remain real,
with no loss of energy under the physical spectral realization. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Complex ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
noncomputable section

/-- Differentiation preserves spectral reality for the actual filtered
characters. This follows from their strong derivative, not a formal multiplier. -/
theorem old_signed_projected_derivative_real (b : ℝ) (x : Vec 2) (i j k : Fin 2) :
    oldSignedSpectralReality b (oldSignedProjectedDerivative b x i j k)=
      oldSignedProjectedDerivative b x i j k := by
  have hf := old_signed_projected_character_hasFDerivAt b x i j
  have hr := (oldSignedSpectralReality b).hasFDerivAt.comp x hf
  have he : (fun y => oldSignedSpectralReality b (oldSignedProjectedCharacter b y i j))=
      (fun y => oldSignedProjectedCharacter b y i j) :=
    funext (fun y => old_signed_projected_character_real b y i j)
  change HasFDerivAt (fun y => oldSignedSpectralReality b (oldSignedProjectedCharacter b y i j)) _ x at hr
  rw [he] at hr
  have hh := congrArg (fun D : Vec 2 →L[ℝ] Lp ℂ 2 (q3SpectralMeasure b) => D (basisVec k)) (hr.unique hf)
  fin_cases k <;> simpa [ContinuousLinearMap.comp_apply,oldSignedProjectedSpatialDerivative,basisVec,Pi.single_apply] using hh

/-- Every spectral-real input is represented by its full real white image. -/
theorem old_signed_potential_white_map_complexify (b : ℝ) (L : {l : ℝ // 0 < l})
    (f : Lp ℂ 2 (q3SpectralMeasure b)) (hf : oldSignedSpectralReality b f=f) :
    oldSignedWhiteComplexify (oldSignedPotentialWhiteMap b L f)=oldSignedSpectralWhiteInverse b L f := by
  change oldSignedWhiteComplexify (oldSignedWhiteRealPart (oldSignedSpectralWhiteInverse b L f))=
    oldSignedSpectralWhiteInverse b L f
  apply old_signed_white_complexify_real_part
  simpa only [hf] using (old_signed_spectral_white_reality b L f).symm

/-- Actual white kernel for a dimensionless spatial derivative. -/
def oldSignedProjectedDerivativeWhiteKernel (b : ℝ) (L : {l : ℝ // 0 < l})
    (x : Vec 2) (i j k : Fin 2) : WhiteNoise :=
  oldSignedPotentialWhiteMap b L (oldSignedProjectedDerivative b x i j k)

/-- The actual real projected kernel has its strong spatial derivative
under the same physical spectral-to-white map. -/
theorem old_signed_projected_white_hasFDerivAt (b : ℝ) (L : {l : ℝ // 0 < l})
    (x : Vec 2) (i j : Fin 2) :
    HasFDerivAt (fun y => oldSignedProjectedWhiteKernel b L y i j)
      ((oldSignedPotentialWhiteMap b L).comp (oldSignedProjectedSpatialDerivative b x i j)) x :=
  (oldSignedPotentialWhiteMap b L).hasFDerivAt.comp x (old_signed_projected_character_hasFDerivAt b x i j)

end
end ASDExplicitGamma.Native
