module

public import ASDExplicitGamma.Native.OldSignedPhysicalFluxTrace
public import ASDExplicitGamma.Native.OldSignedDirectionalDepthTraceBound

/-! Directional complementary matrices for the actual physical flux. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Triadic
noncomputable section

/-- Pure load in either diagonal block. -/
def oldSignedDirectionalLoad (bottom : Bool) (e : Vec 2) : BlockVec 2 :=
  if bottom then (0,e) else (e,0)

/-- The exact directional complementary matrix, before averaging in law. -/
def oldSignedPhysicalFluxDepthMatrix (Q : TriadicCube 2) (depth : ℕ) (a : CoeffField 2)
    (bottom : Bool) : Mat 2 :=
  let A := coarseBlockMatrix (openCubeSet Q) a
  let B := descendantsAverageBlockMat Q depth (fun U => coarseBlockMatrix (openCubeSet U) a)
  if bottom then A.lowerRight+B.upperLeft-(2:ℝ) • (1:Mat 2)
  else A.upperLeft+B.lowerRight-(2:ℝ) • (1:Mat 2)

/-- The full complementary energy in a pure direction is exactly its
physical directional quadratic form. -/
theorem old_signed_physical_flux_directional_energy (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (bottom : Bool) (e : Vec 2) :
    let P := oldSignedDirectionalLoad bottom e
    let S : Vec 2 → BlockVec 2 := oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P
    let L := oldSignedLocalResidual Q depth nu sigma hnu hsigma k (fun _ => P.swap) (memLp_const P.swap)
    oldSignedEnergyPairing Q nu sigma k (oldSignedDualReflection Q nu sigma k S-L)
      (oldSignedDualReflection Q nu sigma k S-L)=
      vecDot e (matVecMul (oldSignedPhysicalFluxDepthMatrix Q depth
        (responseFramePlanarCoefficientField nu sigma k) bottom) e) := by
  intro P S L
  rw [old_signed_reciprocal_patch_energy Q depth nu sigma hnu hsigma k P P.swap,
    ←blockVecDot_blockMatVecMul_descendantsAverageBlockMat]
  cases bottom <;>
    simp [P,oldSignedDirectionalLoad,oldSignedPhysicalFluxDepthMatrix,blockVecDot,blockMatVecMul,
      matVecMul,vecDot,Fin.sum_univ_two,Matrix.one_apply] <;> ring

/-- Nonnegative complementary energy makes both directional matrices positive. -/
theorem old_signed_physical_flux_directional_nonneg (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (bottom : Bool) (e : Vec 2) :
    0 ≤ vecDot e (matVecMul (oldSignedPhysicalFluxDepthMatrix Q depth
      (responseFramePlanarCoefficientField nu sigma k) bottom) e) := by
  rw [←old_signed_physical_flux_directional_energy Q depth nu sigma hnu hsigma k bottom e]
  exact old_signed_energy_pairing_nonneg Q nu sigma hnu hsigma k _

/-- The two directional matrix traces add to the exact parent and child defects. -/
theorem old_signed_physical_flux_directional_trace_sum (Q : TriadicCube 2) (depth : ℕ)
    (a : CoeffField 2) :
    Matrix.trace (oldSignedPhysicalFluxDepthMatrix Q depth a false)+
      Matrix.trace (oldSignedPhysicalFluxDepthMatrix Q depth a true)=
    traceDefect (openCubeSet Q) a 1+
      descendantsAverage Q depth (fun U => traceDefect (openCubeSet U) a 1) := by
  have hh := old_signed_paired_depth_matrix_trace Q depth a
  simp only [oldSignedPhysicalFluxDepthMatrix,Bool.false_eq_true,ite_false,ite_true,
    Matrix.trace_add,Matrix.trace_sub,Matrix.trace_smul,smul_eq_mul]
  simp only [oldSignedPairedDepthMatrix,Matrix.trace_add,Matrix.trace_sub,Matrix.trace_smul,smul_eq_mul] at hh
  rw [←hh]
  simp only [traceDefect,inv_one,one_mul]
  norm_num
  ring

/-- A nonnegative planar quadratic form has nonnegative trace. -/
theorem old_signed_nonnegative_quadratic_trace_nonneg (A : Mat 2)
    (hA : ∀ e : Vec 2,0 ≤ vecDot e (matVecMul A e)) : 0 ≤ Matrix.trace A := by
  have h0 := hA ![1,0]
  have h1 := hA ![0,1]
  norm_num [vecDot,matVecMul,Fin.sum_univ_two] at h0 h1
  simpa only [Matrix.trace_fin_two] using add_nonneg h0 h1

/-- Each directional complementary trace is bounded by the sum of the two
nonnegative traces; no isotropy or pathwise half factor is asserted. -/
theorem old_signed_physical_flux_directional_trace_bound (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (bottom : Bool) :
    let a := responseFramePlanarCoefficientField nu sigma k
    Matrix.trace (oldSignedPhysicalFluxDepthMatrix Q depth a bottom) ≤
      traceDefect (openCubeSet Q) a 1+
        descendantsAverage Q depth (fun U => traceDefect (openCubeSet U) a 1) := by
  intro a
  have ho := old_signed_nonnegative_quadratic_trace_nonneg
    (oldSignedPhysicalFluxDepthMatrix Q depth a (!bottom))
    (old_signed_physical_flux_directional_nonneg Q depth nu sigma hnu hsigma k (!bottom))
  have hs := old_signed_physical_flux_directional_trace_sum Q depth a
  cases bottom <;> simp only [Bool.not_true,Bool.not_false] at ho
  all_goals linarith only [ho,hs]

/-- The sharp pathwise directional quadratic payment needed for the
physical-flux affine source, obtained from the full complementary trace. -/
theorem old_signed_physical_flux_directional_two_trace_bound (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (bottom : Bool) (e : Vec 2) :
    let a := responseFramePlanarCoefficientField nu sigma k
    vecDot e (matVecMul (oldSignedPhysicalFluxDepthMatrix Q depth a bottom) e) ≤
      2*descendantsAverage Q depth (fun U => traceDefect (openCubeSet U) a 1)*vecNormSq e := by
  intro a
  have hq := old_signed_nonnegative_quadratic_le_trace
    (oldSignedPhysicalFluxDepthMatrix Q depth a bottom)
    (old_signed_physical_flux_directional_nonneg Q depth nu sigma hnu hsigma k bottom) e
  have ht := old_signed_physical_flux_directional_trace_bound Q depth nu sigma hnu hsigma k bottom
  have hp := old_signed_parent_trace_le_child Q depth nu sigma hnu hsigma k
  have hc : Matrix.trace (oldSignedPhysicalFluxDepthMatrix Q depth a bottom) ≤
      2*descendantsAverage Q depth (fun U => traceDefect (openCubeSet U) a 1) := by
    linarith only [ht,hp]
  exact hq.trans (mul_le_mul_of_nonneg_right hc (vecNormSq_nonneg e))

end
end ASDExplicitGamma.Native
