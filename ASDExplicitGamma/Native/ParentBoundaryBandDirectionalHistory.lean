module

public import ASDExplicitGamma.Native.ParentBoundaryBandDepthSeries
public import ASDExplicitGamma.Native.ParentBoundaryBandTraceMoments
public import ASDExplicitGamma.Native.OldSignedSourceDirectionalPayment
public import ASDExplicitGamma.Native.OldSignedNonnegativeSeriesIntegral
public import ASDExplicitGamma.Native.OldSignedDirectionalWeakProxy

/-! The complete actual inverse-weighted directional history, with honest
integrability and the annealed half-trace budget. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Inverse Variational Algsuperdiff.Section3
noncomputable section

/-- The actual directional history term, on the common OLD descendant tiling. -/
def parentBoundaryBandDirectionalHistoryTerm (M : ABKModel 2) (n : ℤ) (height : ℕ) (U : TriadicCube 2) (t : ℝ)
    (e : Vec 2) (j : ℕ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  inverseHistoryDiscount^(2*j)*
    (lemmaVInverseDepthMax U (parentBoundaryBandFrameField M n height t ω) j*
      vecDot e (matVecMul (oldSignedPairedDepthMatrix U j
        (parentBoundaryBandFrameField M n height t ω)) e))

/-- Every actual directional term is nonnegative. -/
theorem parent_boundary_band_directional_history_term_nonneg
    (M : ABKModel 2) (n : ℤ) (height : ℕ) (r : ℕ) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth (originCube 2 n) r) (t : ℝ) (e : Vec 2) (j : ℕ)
    (ω : Cutoff.CutoffSample 2) : 0 ≤ parentBoundaryBandDirectionalHistoryTerm M n height U t e j ω :=
  mul_nonneg (pow_nonneg inverse_history_discount_range.1.le _)
    (mul_nonneg (lemmaVInverseDepthMax_nonneg _ _ _)
      (parent_boundary_band_directional_nonneg_le M n height r U hU t ω j e).1)

/-- The directional series converges samplewise by domination by the actual
complete trace proxy, before any expectation is taken. -/
theorem parent_boundary_band_directional_history_summable
    (M : ABKModel 2) (n : ℤ) (height : ℕ) (r : ℕ) (U : TriadicCube 2)
    (hU : U ∈ descendantsAtDepth (originCube 2 n) r) (t : ℝ)
    (e : Vec 2) (ω : Cutoff.CutoffSample 2) :
    Summable (fun j => parentBoundaryBandDirectionalHistoryTerm M n height U t e j ω) := by
  let a := parentBoundaryBandFrameField M n height t ω
  have hEll := (responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet (originCube 2 n)) M.nu (Annealed.sigmaBar M n) M.nu_pos
    (Annealed.sigmaBar_characterization M n).1 (pureFluxOpenResponseRestriction n (nativeSourceBandScalar n height t ω))).mono
    (measurableSet_openCubeSet U) (openCubeSet_subset_of_mem_descendantsAtDepth hU)
  have hs := (old_signed_weak_trace_proxy_summable U a hEll).mul_right (vecNormSq e)
  apply Summable.of_nonneg_of_le
    (fun j => parent_boundary_band_directional_history_term_nonneg M n height r U hU t e j ω) _ hs
  intro j
  have hh := mul_le_mul_of_nonneg_left
    (parent_boundary_band_directional_nonneg_le M n height r U hU t ω j e).2
    (mul_nonneg (pow_nonneg inverse_history_discount_range.1.le (2*j))
      (lemmaVInverseDepthMax_nonneg U a j))
  rw [←parent_boundary_band_cell_trace_eq M n height r U hU t ω j] at hh
  exact (by simpa only [parentBoundaryBandDirectionalHistoryTerm,mul_assoc,a] using hh)

end
end ASDExplicitGamma.Native
