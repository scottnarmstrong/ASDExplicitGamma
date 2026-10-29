module

public import ASDExplicitGamma.Native.OldSignedFlatMeans
public import ASDExplicitGamma.Scalar.FullResponseNorm

/-! The actual signed affine mean contribution of AN (5.2). Absolute
bounds below prove convergence only; the exported contribution keeps its sign. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Scalar
noncomputable section

/-- Absolute quadratic control for an arbitrary actual block matrix. No
positivity of its deviation from the identity is assumed. -/
theorem old_signed_block_quadratic_abs_le (A : BlockMat 2) (P : BlockVec 2) :
    |blockVecDot P (blockMatVecMul A P)|≤‖HilbertBlockVec.applyBlockMat A‖*blockVecDot P P := by
  let x := HilbertBlockVec.ofBlockVec P
  let B := HilbertBlockVec.applyBlockMat A
  have hi := abs_real_inner_le_norm x (B x)
  have hb := mul_le_mul_of_nonneg_left (B.le_opNorm x) (norm_nonneg x)
  have hh : ‖x‖*‖B x‖≤‖B‖*‖x‖^2 := hb.trans_eq (by ring)
  simpa only [x,B,HilbertBlockVec.inner_ofBlockVec_applyBlockMat,HilbertBlockVec.norm_sq_ofBlockVec] using hi.trans hh

/-- The identity-subtracted affine form is absolutely controlled by the
actual mean size, while its pathwise sign remains unrestricted. -/
theorem old_signed_affine_deviation_abs_le (A : BlockMat 2) (P : BlockVec 2) :
    |blockVecDot P (blockMatVecMul A P)-blockVecDot P P|≤
      (‖HilbertBlockVec.applyBlockMat A‖+1)*blockVecDot P P := by
  have hp : 0≤blockVecDot P P := add_nonneg (vecNormSq_nonneg _) (vecNormSq_nonneg _)
  calc
    _ ≤ |blockVecDot P (blockMatVecMul A P)|+|blockVecDot P P| := abs_sub _ _
    _ ≤ ‖HilbertBlockVec.applyBlockMat A‖*blockVecDot P P+blockVecDot P P := by
      rw [abs_of_nonneg hp]
      exact add_le_add (old_signed_block_quadratic_abs_le A P) le_rfl
    _ = _ := by ring

/-- Genuine summability of the signed affine form follows from the
actual complete mean-square series, without a sign hypothesis. -/
theorem old_signed_affine_deviation_summable {I : Type*} (A : BlockMat 2) (P : I → BlockVec 2)
    (hs : Summable (fun n => blockVecDot (P n) (P n))) :
    Summable (fun n => blockVecDot (P n) (blockMatVecMul A (P n))-blockVecDot (P n) (P n)) := by
  have hh := (hs.mul_left (‖HilbertBlockVec.applyBlockMat A‖+1)).of_nonneg_of_le
    (fun n => abs_nonneg _) (fun n => old_signed_affine_deviation_abs_le A (P n))
  exact Summable.of_norm (by simpa only [Real.norm_eq_abs] using hh)

/-- One actual cell's signed mean bill, with both flat inputs in the
same physical coarse response matrix. The subtraction is m.I.m. -/
def oldSignedFlatAffineCellMode (Q U : TriadicCube 2) (a : CoeffField 2)
    (b : ℝ) (L : {l : ℝ // 0<l}) (n : whiteBasisIndex) : ℝ :=
  ∑ i : Fin 2, (
    (let p := oldSignedBlockMean U (oldSignedFlatPlusBlock Q b L n i)
     blockVecDot p (blockMatVecMul (coarseBlockMatrix (openCubeSet U) a) p)-blockVecDot p p)+
    (let p := oldSignedBlockMean U (oldSignedFlatMinusBlock Q b L n i)
     blockVecDot p (blockMatVecMul (coarseBlockMatrix (openCubeSet U) a) p)-blockVecDot p p))

/-- The actual normalized finite partition average of the signed affine bill. -/
def oldSignedFlatAffineMode (Q : TriadicCube 2) (depth : ℕ) (a : CoeffField 2)
    (b : ℝ) (L : {l : ℝ // 0<l}) (n : whiteBasisIndex) : ℝ :=
  descendantsAverage Q depth (fun U => oldSignedFlatAffineCellMode Q U a b L n)

/-- AN (5.2), summed over the complete physical fresh direction family. -/
def oldSignedFlatAffineContribution (Q : TriadicCube 2) (depth : ℕ) (a : CoeffField 2)
    (b : ℝ) (L : {l : ℝ // 0<l}) : ℝ :=
  ∑' n,oldSignedFlatAffineMode Q depth a b L n

/-- The actual signed cell bill is a genuinely convergent mode series. -/
theorem old_signed_flat_affine_cell_summable (Q : TriadicCube 2) (depth : ℕ) (a : CoeffField 2)
    (b : ℝ) (L : {l : ℝ // 0<l}) (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) :
    Summable (oldSignedFlatAffineCellMode Q U a b L) := by
  let Ap := fun n i =>
    let p := oldSignedBlockMean U (oldSignedFlatPlusBlock Q b L n i)
    blockVecDot p (blockMatVecMul (coarseBlockMatrix (openCubeSet U) a) p)-blockVecDot p p
  let Am := fun n i =>
    let p := oldSignedBlockMean U (oldSignedFlatMinusBlock Q b L n i)
    blockVecDot p (blockMatVecMul (coarseBlockMatrix (openCubeSet U) a) p)-blockVecDot p p
  have hp (i : Fin 2) : Summable (fun n => Ap n i) :=
    old_signed_affine_deviation_summable (coarseBlockMatrix (openCubeSet U) a)
      (fun n => oldSignedBlockMean U (oldSignedFlatPlusBlock Q b L n i))
      (old_signed_flat_plus_mean_series Q depth b L i U hU)
  have hm (i : Fin 2) : Summable (fun n => Am n i) :=
    old_signed_affine_deviation_summable (coarseBlockMatrix (openCubeSet U) a)
      (fun n => oldSignedBlockMean U (oldSignedFlatMinusBlock Q b L n i))
      (old_signed_flat_minus_mean_series Q depth b L i U hU)
  change Summable (fun n => ∑ i : Fin 2,(Ap n i+Am n i))
  exact summable_sum (fun i _ => (hp i).add (hm i))

/-- The actual signed Aff series is summable on the finite partition. -/
theorem old_signed_flat_affine_summable (Q : TriadicCube 2) (depth : ℕ) (a : CoeffField 2)
    (b : ℝ) (L : {l : ℝ // 0<l}) : Summable (oldSignedFlatAffineMode Q depth a b L) := by
  classical
  have hs : Summable (fun n => ∑ U ∈ descendantsAtDepth Q depth,oldSignedFlatAffineCellMode Q U a b L n) :=
    summable_sum (fun U hU => old_signed_flat_affine_cell_summable Q depth a b L U hU)
  change Summable (fun n => (((descendantsAtDepth Q depth).card : ℝ)⁻¹)*
    ∑ U ∈ descendantsAtDepth Q depth,oldSignedFlatAffineCellMode Q U a b L n)
  exact hs.mul_left (((descendantsAtDepth Q depth).card : ℝ)⁻¹)

end
end ASDExplicitGamma.Native
