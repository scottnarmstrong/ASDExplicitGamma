module

public import ASDExplicitGamma.Native.OldSignedCanonicalPotentials
public import ASDExplicitGamma.Native.OldSignedPointwiseShear
public import ASDExplicitGamma.Main.Q3W2Jets
public import ASDExplicitGamma.Triadic.DiagAffine
public import ASDExplicitGamma.Triadic.PlanarDirectionVolume

/-! The actual localized OLD-error source in AN (1.1) and (4.1), with
genuine L2 data and its full parent shear-gauge variation supplied. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Main
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Response ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
noncomputable section

/-- Actual localized pure-second source on the canonical old error. -/
def oldSignedOldErrorSource (Q : TriadicCube 2) (mesh : ℕ) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (b : ℝ) (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) (P : BlockVec 2) : Vec 2 → BlockVec 2 :=
  oldSignedLocalizedPotentialShear (diagInterpolant Q mesh)
    (mainQ3DirectionW2 Q b L (whiteBasis n)).value
    (oldSignedCanonicalFirstCorrector Q a hEll P).toH1Function

/-- Actual interpolation of the canonical error has the required zero-trace
residual; it is not an extra premise on the OLD source. -/
theorem old_signed_old_error_interpolation_residual (Q : TriadicCube 2) (mesh : ℕ)
    (a : CoeffField 2) {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (P : BlockVec 2) :
    MemH10 (openCubeSet Q) ((oldSignedCanonicalFirstCorrector Q a hEll P).toH1Function-
      diagInterpolant Q mesh (oldSignedCanonicalFirstCorrector Q a hEll P).toH1Function).toFun := by
  simpa only [H1Function.sub_toFun] using
    memH10_sub (oldSignedCanonicalFirstCorrector Q a hEll P).memH10
      (diagInterpolant_h10_memH10 Q mesh (oldSignedCanonicalFirstCorrector Q a hEll P))

/-- The actual localized old-error source is a genuine L2 doubled field. -/
theorem old_signed_old_error_source_memL2 (Q : TriadicCube 2) (mesh : ℕ) (a : CoeffField 2)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (b : ℝ) (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) (P : BlockVec 2) :
    MemBlockL2 (openCubeSet Q) (oldSignedOldErrorSource Q mesh a hEll b L n P) :=
  old_signed_localized_potential_shear_memL2 Q (diagInterpolant Q mesh) _ _
    (mainQ3DirectionW2 Q b L (whiteBasis n)).value_memLp_top
    (mainQ3DirectionW2 Q b L (whiteBasis n)).gradient_memLp_top_volume

/-- The complete parent gauge correction for the actual old-error source
is an admissible variation. No source patch or boundary flux is discarded. -/
theorem old_signed_old_error_source_gauge_variation (Q : TriadicCube 2) (mesh : ℕ)
    (a : CoeffField 2) {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (b : ℝ) (L : {l : ℝ // 0 < l}) (n : whiteBasisIndex) (P : BlockVec 2) :
    ScalarVariation (openCubeSet Q) (oldSignedOldErrorSource Q mesh a hEll b L n P-
      oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
        ((oldSignedCanonicalAffineField Q a hEll P : Vec 2 → BlockVec 2)-(fun _ => P))) := by
  let eta := (mainQ3DirectionW2 Q b L (whiteBasis n)).value
  let phi := (oldSignedCanonicalFirstCorrector Q a hEll P).toH1Function
  have ht := old_signed_localized_physical_shear_variation Q (diagInterpolant Q mesh) eta phi
    (old_signed_old_error_interpolation_residual Q mesh a hEll P)
    (mainQ3DirectionW2 Q b L (whiteBasis n)).value_memLp_top
    (mainQ3DirectionW2 Q b L (whiteBasis n)).gradient_memLp_top_volume
  have hgrad : phi.grad=fun x => (oldSignedCanonicalAffineField Q a hEll P x).1-P.1 :=
    old_signed_canonical_first_corrector_grad Q a hEll P
  have hc : oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
      ((oldSignedCanonicalAffineField Q a hEll P : Vec 2 → BlockVec 2)-(fun _ => P))=
        oldSignedPhysicalPotentialShear eta phi := by
    funext x
    change (0,-(eta x • matVecMul responsePlanarJ
      ((oldSignedCanonicalAffineField Q a hEll P x).1-P.1)))=
        (0,-(eta x • matVecMul responsePlanarJ (phi.grad x)))
    rw [hgrad]
  rw [hc]
  exact ht

end
end ASDExplicitGamma.Native
