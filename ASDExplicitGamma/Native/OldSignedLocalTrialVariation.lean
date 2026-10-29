module

public import ASDExplicitGamma.Native.OldSignedCellProjection

/-! Exact actual cell-projection trial membership, allowing the localized
and physical shear to differ by their proved zero-normal gauge variation. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Response
noncomputable section

/-- The actual AN (4.1) three-term local residual is a parent variation
after subtracting the physical shear of the old minimizer. The source
hypotheses are literal membership facts, not energy estimates. -/
theorem old_signed_local_flat_trial_variation (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (C : (Vec 2 → BlockVec 2) →ₗ[ℝ] (Vec 2 → BlockVec 2))
    (S E Fplus Fold Fminus : Vec 2 → BlockVec 2)
    (hp : MemBlockL2 (openCubeSet Q) Fplus)
    (ho : MemBlockL2 (openCubeSet Q) Fold)
    (hm : MemBlockL2 (openCubeSet Q) Fminus)
    (hplus : ScalarVariation (openCubeSet Q) (Fplus-C E))
    (hgauge : ScalarVariation (openCubeSet Q) (Fold-C (S-E)))
    (hminus : ScalarVariation (openCubeSet Q) Fminus) :
    ScalarVariation (openCubeSet Q)
      (oldSignedLocalResidual Q depth nu sigma hnu hsigma k Fplus hp+
        oldSignedLocalResidual Q depth nu sigma hnu hsigma k Fold ho-
        oldSignedLocalResidual Q depth nu sigma hnu hsigma k Fminus hm-C S) := by
  let V := correctionFieldSubmodule (openCubeSet Q)
  let A := oldSignedLocalResidual Q depth nu sigma hnu hsigma k Fplus hp
  let R := oldSignedLocalResidual Q depth nu sigma hnu hsigma k Fold ho
  let Z := oldSignedLocalResidual Q depth nu sigma hnu hsigma k Fminus hm
  have hPA := old_signed_local_removed_variation Q depth nu sigma hnu hsigma k Fplus hp
  have hOR := old_signed_local_removed_variation Q depth nu sigma hnu hsigma k Fold ho
  have hMZ := old_signed_local_removed_variation Q depth nu sigma hnu hsigma k Fminus hm
  change Fplus-A ∈ V at hPA
  change Fold-R ∈ V at hOR
  change Fminus-Z ∈ V at hMZ
  change Fplus-C E ∈ V at hplus
  change Fold-C (S-E) ∈ V at hgauge
  change Fminus ∈ V at hminus
  change A+R-Z-C S ∈ V
  have hh := V.add_mem
    (V.sub_mem (V.sub_mem (V.sub_mem (V.add_mem hplus hgauge) hminus) hPA) hOR) hMZ
  convert hh using 1
  rw [map_sub]
  abel

/-- The actual projection of the zero source is itself a parent variation,
without identifying arbitrary L2 representatives pointwise with zero. -/
theorem old_signed_local_zero_residual_variation (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) :
    ScalarVariation (openCubeSet Q)
      (oldSignedLocalResidual Q depth nu sigma hnu hsigma k 0 MemLp.zero) := by
  have hh := old_signed_local_removed_variation Q depth nu sigma hnu hsigma k 0 MemLp.zero
  change (0-oldSignedLocalResidual Q depth nu sigma hnu hsigma k 0 MemLp.zero) ∈
    correctionFieldSubmodule (openCubeSet Q) at hh
  rw [zero_sub] at hh
  exact (correctionFieldSubmodule (openCubeSet Q)).neg_mem_iff.mp hh

/-- The actual top-load two-term local trial is admissible, including the
localized old-error gauge and all actual cell projection corrections. -/
theorem old_signed_local_top_trial_variation (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (C : (Vec 2 → BlockVec 2) →ₗ[ℝ] (Vec 2 → BlockVec 2))
    (S E Fplus Fold : Vec 2 → BlockVec 2)
    (hp : MemBlockL2 (openCubeSet Q) Fplus) (ho : MemBlockL2 (openCubeSet Q) Fold)
    (hplus : ScalarVariation (openCubeSet Q) (Fplus-C E))
    (hgauge : ScalarVariation (openCubeSet Q) (Fold-C (S-E))) :
    ScalarVariation (openCubeSet Q)
      (oldSignedLocalResidual Q depth nu sigma hnu hsigma k Fplus hp+
        oldSignedLocalResidual Q depth nu sigma hnu hsigma k Fold ho-C S) := by
  let V := correctionFieldSubmodule (openCubeSet Q)
  have hh := old_signed_local_flat_trial_variation Q depth nu sigma hnu hsigma k
    C S E Fplus Fold 0 hp ho MemLp.zero hplus hgauge (scalar_variation_zero _)
  have hz := old_signed_local_zero_residual_variation Q depth nu sigma hnu hsigma k
  change _ ∈ V at hh
  change _ ∈ V at hz
  change _ ∈ V
  convert V.add_mem hh hz using 1
  abel

/-- The bottom-load trial retains its minus sign and has no plus input;
the physical affine shear is zero on a pure bottom load. -/
theorem old_signed_local_bottom_trial_variation (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    (C : (Vec 2 → BlockVec 2) →ₗ[ℝ] (Vec 2 → BlockVec 2))
    (S E Fold Fminus : Vec 2 → BlockVec 2)
    (ho : MemBlockL2 (openCubeSet Q) Fold) (hm : MemBlockL2 (openCubeSet Q) Fminus)
    (hE : C E=0) (hgauge : ScalarVariation (openCubeSet Q) (Fold-C (S-E)))
    (hminus : ScalarVariation (openCubeSet Q) Fminus) :
    ScalarVariation (openCubeSet Q)
      (oldSignedLocalResidual Q depth nu sigma hnu hsigma k Fold ho-
        oldSignedLocalResidual Q depth nu sigma hnu hsigma k Fminus hm-C S) := by
  let V := correctionFieldSubmodule (openCubeSet Q)
  have hplus : ScalarVariation (openCubeSet Q) (0-C E) := by
    rw [hE,sub_self]
    exact scalar_variation_zero _
  have hh := old_signed_local_flat_trial_variation Q depth nu sigma hnu hsigma k
    C S E 0 Fold Fminus MemLp.zero ho hm hplus hgauge hminus
  have hz := old_signed_local_zero_residual_variation Q depth nu sigma hnu hsigma k
  change _ ∈ V at hh
  change _ ∈ V at hz
  change _ ∈ V
  convert V.sub_mem hh hz using 1
  abel

end
end ASDExplicitGamma.Native
