module

public import ASDExplicitGamma.Native.OldSignedPotentialRegularity
public import ASDExplicitGamma.Native.OldSignedWhiteProjectedKernel

/-! Actual physical potentials for the whole-plane projected white modes.
The shell-length factors cancel in their gradients. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Complex ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
noncomputable section

/-- Real spectral-to-white map used for the physical potential. -/
def oldSignedPotentialWhiteMap (b : ℝ) (L : {l : ℝ // 0 < l}) :
    Lp ℂ 2 (q3SpectralMeasure b) →L[ℝ] WhiteNoise :=
  oldSignedWhiteRealPart.comp ((oldSignedSpectralWhiteInverse b L).toContinuousLinearMap.restrictScalars ℝ)

/-- A scalar potential for one physical whole-plane projected load. The
normalization is at spatial zero; its gradient is independent of that choice. -/
def oldSignedPhysicalModePotential (b : ℝ) (L : {l : ℝ // 0 < l}) (w : WhiteNoise)
    (j : Fin 2) (x : Vec 2) : ℝ :=
  L.1*inner ℝ w (oldSignedPotentialWhiteMap b L (oldSignedSpectralPotential b (L.1⁻¹ • x) j))

/-- The physical mode potential is globally C1, including its dependence
on the actual white direction w. -/
theorem old_signed_physical_mode_potential_contDiff (b : ℝ) (L : {l : ℝ // 0 < l})
    (w : WhiteNoise) (j : Fin 2) : ContDiff ℝ 1 (oldSignedPhysicalModePotential b L w j) := by
  have hs : ContDiff ℝ 1 (fun x : Vec 2 => L.1⁻¹ • x) := by
    exact (L.1⁻¹ • (ContinuousLinearMap.id ℝ (Vec 2))).contDiff
  have hp := (old_signed_spectral_potential_contDiff b j).comp hs
  exact contDiff_const.mul ((innerSL ℝ w).contDiff.comp ((oldSignedPotentialWhiteMap b L).contDiff.comp hp))

/-- The physical gradient, expressed as the exact projected white kernel,
not as an arbitrary recovery representative. -/
def oldSignedPhysicalModeDerivative (b : ℝ) (L : {l : ℝ // 0 < l})
    (w : WhiteNoise) (j : Fin 2) (x : Vec 2) : Vec 2 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj 0).smulRight
    (inner ℝ w (oldSignedProjectedWhiteKernel b L (L.1⁻¹ • x) 0 j))+
  (ContinuousLinearMap.proj 1).smulRight
    (inner ℝ w (oldSignedProjectedWhiteKernel b L (L.1⁻¹ • x) 1 j))

/-- No scalar-frame or length factor is lost on passing from the spectral
potential to its physical projected mode. -/
theorem old_signed_physical_mode_potential_hasFDerivAt (b : ℝ) (L : {l : ℝ // 0 < l})
    (w : WhiteNoise) (j : Fin 2) (x : Vec 2) :
    HasFDerivAt (oldSignedPhysicalModePotential b L w j)
      (oldSignedPhysicalModeDerivative b L w j x) x := by
  have hs := ((ContinuousLinearMap.id ℝ (Vec 2)).hasFDerivAt (x := x)).const_smul L.1⁻¹
  have hp := (old_signed_spectral_potential_hasFDerivAt b (L.1⁻¹ • x) j).comp x hs
  have hw := (oldSignedPotentialWhiteMap b L).hasFDerivAt.comp x hp
  have hh := (((innerSL ℝ w).hasFDerivAt).comp x hw).const_mul L.1
  change HasFDerivAt (oldSignedPhysicalModePotential b L w j) _ x at hh
  convert hh using 1
  ext v
  simp only [oldSignedPhysicalModeDerivative,oldSignedSpectralPotentialDerivative,
    add_apply,ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.comp_apply,smul_apply,ContinuousLinearMap.id_apply,
    smul_eq_mul,map_add,map_smul]
  change v 0*inner ℝ w (oldSignedProjectedWhiteKernel b L (L.1⁻¹ • x) 0 j)+
    v 1*inner ℝ w (oldSignedProjectedWhiteKernel b L (L.1⁻¹ • x) 1 j)=_
  dsimp only [oldSignedPotentialWhiteMap,oldSignedProjectedWhiteKernel]
  field_simp [L.2.ne']
  rfl

end
end ASDExplicitGamma.Native
