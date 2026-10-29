module

public import ASDExplicitGamma.Native.OldSignedFlatAffine
public import ASDExplicitGamma.Variational.Subadditivity
public import ASDExplicitGamma.Variational.LemmaVH1
public import ASDExplicitGamma.Inverse.FullResponseMatrixError
public import ASDExplicitGamma.Inverse.RawWeakHistory
public import ASDExplicitGamma.Variational.CompatibleCoercivity
public import ASDExplicitGamma.Native.OldSignedHistoryComparison
public import ASDExplicitGamma.Cold.CoarseGramDefect
public import Homogenization.Book.Ch05.Theorems.Section56.VarianceEstimateQuadratic.MatrixTools

/-! Scale-by-scale comparison of the actual OLD affine minimizers. -/
@[expose] public section

namespace ASDExplicitGamma.Native

open Homogenization MeasureTheory Response Scalar Triadic Variational

private theorem old_signed_cubeAverage_sub (Q : TriadicCube 2)
    {f g : Vec 2 → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hg : MemLp g 2 (normalizedCubeMeasure Q)) :
    cubeAverage Q (fun x => f x - g x) = cubeAverage Q f - cubeAverage Q g := by
  rw [cubeAverage_eq_integral_normalizedCubeMeasure,
    cubeAverage_eq_integral_normalizedCubeMeasure,
    cubeAverage_eq_integral_normalizedCubeMeasure]
  exact integral_sub (hf.integrable (by norm_num)) (hg.integrable (by norm_num))

private theorem old_signed_cubeAverage_congr_ae (Q : TriadicCube 2)
    {f g : Vec 2 → ℝ}
    (hfg : f =ᵐ[volumeMeasureOn (openCubeSet Q)] g) :
    cubeAverage Q f = cubeAverage Q g := by
  rw [cubeAverage_eq_integralAverage_openCubeSet,
    cubeAverage_eq_integralAverage_openCubeSet]
  unfold integralAverage
  congr 1
  exact integral_congr_ae hfg

/-- The first-coordinate mean of a genuine variation is zero because it has
an actual H10 potential on the square. -/
private theorem old_signed_variation_first_mean_zero (Q : TriadicCube 2)
    {F : Vec 2 → BlockVec 2} (hF : ScalarVariation (openCubeSet Q) F)
    (i : Fin 2) :
    cubeAverage Q (fun x => (F x).1 i) = 0 := by
  obtain ⟨u, hu⟩ := hF.2.1
  calc
    cubeAverage Q (fun x => (F x).1 i) =
        cubeAverage Q (fun x => u.toH1Function.grad x i) := by
          apply cubeAverage_congr_on_cubeSet
          intro x hx
          exact congrArg (fun v : Vec 2 => v i) (congrFun hu x).symm
    _ = 0 := Triadic.cubeAverage_h10_gradient_eq_zero Q u i

private theorem old_signed_affine_removed_variation (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    ScalarVariation (openCubeSet Q)
      (fun x => P - scalarResidualField Q nu sigma hnu hsigma k
        ((scalarFrameRealization Q nu sigma hnu hsigma k).constantField P) x) := by
  let hP : MemBlockL2 (openCubeSet Q) (fun _ : Vec 2 => P) := memLp_const P
  let H := (scalarFrameRealization Q nu sigma hnu hsigma k).constantField P
  let R := scalarProjectionResidual Q nu sigma hnu hsigma k H
  have hconst : toHilbertBlockL2OfBlockField hP = H := by
    have hfield : toHilbertBlockL2OfBlockField hP =
        blockVecToHilbertBlockL2Const P := by
      apply Lp.ext
      filter_upwards [coeFn_toHilbertBlockL2OfBlockField hP,
        coeFn_blockVecToHilbertBlockL2Const (U := openCubeSet Q) P] with x hx hy
      exact hx.trans hy.symm
    exact hfield.trans (by rfl)
  have hremoved : H - R ∈
      (scalarFrameRealization Q nu sigma hnu hsigma k).correctionSpace.correctionSpace := by
    rw [← hconst]
    exact scalar_projection_removed_mem Q nu sigma hnu hsigma k
      (toHilbertBlockL2OfBlockField hP)
  have hvariation := old_signed_hilbert_correction_variation Q nu sigma hnu hsigma k
    (H - R) hremoved
  have hsourceField : hilbertBlockL2ToBlockL2 H = toBlockL2 hP := by
    rw [← hconst]
    exact hilbertBlockL2ToBlockL2_toHilbertBlockL2OfBlockField hP
  have hsubField : hilbertBlockL2ToBlockL2 (H - R) =
      hilbertBlockL2ToBlockL2 H - hilbertBlockL2ToBlockL2 R := by
    exact map_sub _ H R
  have hsourceAE : (fun _ : Vec 2 => P) =ᵐ[volumeMeasureOn (openCubeSet Q)]
      toBlockL2 hP := (coeFn_toBlockL2 hP).symm
  have hAE : (fun x => P - scalarResidualField Q nu sigma hnu hsigma k H x) =ᵐ[
      volumeMeasureOn (openCubeSet Q)] hilbertBlockL2ToBlockL2 (H - R) := by
    filter_upwards [hsourceAE,
      (Lp.coeFn_sub (toBlockL2 hP) (hilbertBlockL2ToBlockL2 R))] with x hP' hsub
    change P - hilbertBlockL2ToBlockL2 R x =
      hilbertBlockL2ToBlockL2 (H - R) x
    calc
      P - hilbertBlockL2ToBlockL2 R x =
          toBlockL2 hP x - hilbertBlockL2ToBlockL2 R x := by
        exact congrArg (fun z : BlockVec 2 => z - hilbertBlockL2ToBlockL2 R x) hP'
      _ = (toBlockL2 hP - hilbertBlockL2ToBlockL2 R) x := hsub.symm
      _ = hilbertBlockL2ToBlockL2 (H - R) x := by
        rw [hsubField, hsourceField]
  exact old_signed_scalar_variation_congr_ae hAE.symm hvariation

/-- The actual finite cell projection preserves the affine first-block mean
on every descendant. -/
private theorem old_signed_local_first_mean (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2)
    (R : TriadicCube 2) (hR : R ∈ descendantsAtDepth Q depth) (i : Fin 2) :
    cubeAverage R (fun x =>
      (oldSignedLocalResidual Q depth nu sigma hnu hsigma k
        (fun _ => P) (memLp_const P) x).1 i) = P.1 i := by
  let hRQ := openCubeSet_subset_of_mem_descendantsAtDepth hR
  let Z := oldSignedCellResidual Q R hRQ nu sigma hnu hsigma k
    (fun _ => P) (memLp_const P)
  have hZ : MemBlockL2 (openCubeSet R) Z := Z.property
  have hZcoord : MemLp (fun x => (Z x).1 i) 2 (normalizedCubeMeasure R) :=
    memLp_normalized_of_memL2On
      (memScalarL2_coord_of_memVectorL2 (memVectorL2_fst_of_memBlockL2 hZ) i)
  have hconstCoord : MemLp (fun _ : Vec 2 => P.1 i) 2
      (normalizedCubeMeasure R) := memLp_const (P.1 i)
  have hremovedVar := old_signed_cell_removed_variation Q R hRQ nu sigma
    hnu hsigma k (fun _ => P) (memLp_const P)
  have hzero := old_signed_variation_first_mean_zero R hremovedVar i
  change cubeAverage R (fun x => P.1 i - (Z x).1 i) = 0 at hzero
  have hcellMean : cubeAverage R (fun x => P.1 i - (Z x).1 i) =
      cubeAverage R (fun _ => P.1 i) - cubeAverage R (fun x => (Z x).1 i) :=
    old_signed_cubeAverage_sub R hconstCoord hZcoord
  have hZmean : cubeAverage R (fun x => (Z x).1 i) = P.1 i := by
    rw [hcellMean] at hzero
    simp only [cubeAverage_const] at hzero
    linarith
  have hRestr := old_signed_local_residual_restrict Q depth nu sigma
    hnu hsigma k (fun _ => P) (memLp_const P) R hR
  have hAvg : cubeAverage R (fun x =>
      (oldSignedLocalResidual Q depth nu sigma hnu hsigma k
        (fun _ => P) (memLp_const P) x).1 i) =
      cubeAverage R (fun x => (Z x).1 i) := by
    apply old_signed_cubeAverage_congr_ae R
    exact hRestr.mono fun x hx => congrArg (fun v : BlockVec 2 => v.1 i) hx
  exact hAvg.trans hZmean

private theorem old_signed_pairing_eq_energyBilin (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    {F G : Vec 2 → BlockVec 2}
    (hF : MemBlockL2 (openCubeSet Q) F) (hG : MemBlockL2 (openCubeSet Q) G) :
    oldSignedEnergyPairing Q nu sigma k F G =
      (scalarFrameRealization Q nu sigma hnu hsigma k).energyBilin
        (toHilbertBlockL2OfBlockField hG) (toHilbertBlockL2OfBlockField hF) := by
  have h := scalar_frame_bilinear_field Q nu sigma hnu hsigma k hG hF
  unfold oldSignedEnergyPairing
  exact h.symm

private theorem old_signed_pairing_symm (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    {F G : Vec 2 → BlockVec 2}
    (hF : MemBlockL2 (openCubeSet Q) F) (hG : MemBlockL2 (openCubeSet Q) G) :
    oldSignedEnergyPairing Q nu sigma k F G =
      oldSignedEnergyPairing Q nu sigma k G F := by
  rw [old_signed_pairing_eq_energyBilin Q nu sigma hnu hsigma k hF hG,
    old_signed_pairing_eq_energyBilin Q nu sigma hnu hsigma k hG hF]
  exact (scalarFrameRealization Q nu sigma hnu hsigma k).energySymm _ _

private theorem old_signed_hilbert_sub_field (Q : TriadicCube 2)
    {F G : Vec 2 → BlockVec 2}
    (hF : MemBlockL2 (openCubeSet Q) F) (hG : MemBlockL2 (openCubeSet Q) G) :
    toHilbertBlockL2OfBlockField (hF.sub hG) =
      toHilbertBlockL2OfBlockField hF - toHilbertBlockL2OfBlockField hG := by
  apply Lp.ext
  filter_upwards [coeFn_toHilbertBlockL2OfBlockField (hF.sub hG),
    coeFn_toHilbertBlockL2OfBlockField hF,
    coeFn_toHilbertBlockL2OfBlockField hG,
    MeasureTheory.Lp.coeFn_sub (toHilbertBlockL2OfBlockField hF)
      (toHilbertBlockL2OfBlockField hG)] with x hsub hF' hG' hsub'
  calc
    (toHilbertBlockL2OfBlockField (hF.sub hG)) x =
        hilbertifyBlockField (fun x => F x - G x) x := hsub
    _ = hilbertifyBlockField F x - hilbertifyBlockField G x := by
      apply (HilbertBlockVec.continuousLinearEquivBlockVec 2).injective
      rfl
    _ = (toHilbertBlockL2OfBlockField hF) x -
        (toHilbertBlockL2OfBlockField hG) x := by rw [hF', hG']
    _ = ((toHilbertBlockL2OfBlockField hF) -
        (toHilbertBlockL2OfBlockField hG)) x := hsub'.symm

private theorem old_signed_pairing_sub_left (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q))
    {F G H : Vec 2 → BlockVec 2}
    (hF : MemBlockL2 (openCubeSet Q) F) (hG : MemBlockL2 (openCubeSet Q) G)
    (hH : MemBlockL2 (openCubeSet Q) H) :
    oldSignedEnergyPairing Q nu sigma k (fun x => F x - G x) H =
      oldSignedEnergyPairing Q nu sigma k F H -
        oldSignedEnergyPairing Q nu sigma k G H := by
  change oldSignedEnergyPairing Q nu sigma k (F - G) H = _
  rw [old_signed_pairing_eq_energyBilin Q nu sigma hnu hsigma k
        (hF.sub hG) hH,
      old_signed_hilbert_sub_field Q hF hG,
      old_signed_pairing_eq_energyBilin Q nu sigma hnu hsigma k hF hH,
      old_signed_pairing_eq_energyBilin Q nu sigma hnu hsigma k hG hH]
  simp only [map_sub]

private theorem old_signed_affine_field_const_source (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    toHilbertBlockL2OfBlockField (memLp_const P) =
      (scalarFrameRealization Q nu sigma hnu hsigma k).constantField P := by
  have hconst : toHilbertBlockL2OfBlockField
      (U := openCubeSet Q) (F := fun _ : Vec 2 => P) (memLp_const P) =
        blockVecToHilbertBlockL2Const P := by
    apply Lp.ext
    filter_upwards [coeFn_toHilbertBlockL2OfBlockField (memLp_const P),
      coeFn_blockVecToHilbertBlockL2Const (U := openCubeSet Q) P] with x hx hy
    exact hx.trans hy.symm
  exact hconst.trans (by rfl)

/-- The energy of the difference between the parent affine minimizer and the
finite patch of its actual cell minimizers is exactly the average coarse
energy gap. -/
theorem old_signed_affine_patch_energy_identity (Q : TriadicCube 2)
    (depth : ℕ) (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    oldSignedEnergyPairing Q nu sigma k
      (fun x => scalarResidualField Q nu sigma hnu hsigma k
        ((scalarFrameRealization Q nu sigma hnu hsigma k).constantField P) x -
        oldSignedLocalResidual Q depth nu sigma hnu hsigma k (fun _ => P)
          (memLp_const P) x)
      (fun x => scalarResidualField Q nu sigma hnu hsigma k
        ((scalarFrameRealization Q nu sigma hnu hsigma k).constantField P) x -
        oldSignedLocalResidual Q depth nu sigma hnu hsigma k (fun _ => P)
          (memLp_const P) x) =
      descendantsAverage Q depth (fun R => volumeAverage (openCubeSet R) (fun x =>
        blockVecDot
          (oldSignedLocalResidual Q depth nu sigma hnu hsigma k
            (fun _ => P) (memLp_const P) x)
          (blockMatVecMul (blockCoeffField
            (responseFramePlanarCoefficientField nu sigma k) x)
            (oldSignedLocalResidual Q depth nu sigma hnu hsigma k
              (fun _ => P) (memLp_const P) x)))) -
        oldSignedEnergyPairing Q nu sigma k
          (scalarResidualField Q nu sigma hnu hsigma k
            ((scalarFrameRealization Q nu sigma hnu hsigma k).constantField P))
          (scalarResidualField Q nu sigma hnu hsigma k
            ((scalarFrameRealization Q nu sigma hnu hsigma k).constantField P)) := by
  classical
  let a := responseFramePlanarCoefficientField nu sigma k
  let H := (scalarFrameRealization Q nu sigma hnu hsigma k).constantField P
  let S : Vec 2 → BlockVec 2 := scalarResidualField Q nu sigma hnu hsigma k H
  let F : Vec 2 → BlockVec 2 := fun _ => P
  let L : Vec 2 → BlockVec 2 := oldSignedLocalResidual Q depth nu sigma hnu hsigma k F
    (memLp_const P)
  let D : Vec 2 → BlockVec 2 := fun x => S x - L x
  have hF : MemBlockL2 (openCubeSet Q) F := memLp_const P
  have hL : MemBlockL2 (openCubeSet Q) L :=
    old_signed_local_residual_memLp Q depth nu sigma hnu hsigma k F hF
  have hS : MemBlockL2 (openCubeSet Q) S := Lp.memLp _
  have hD : MemBlockL2 (openCubeSet Q) D := hS.sub hL
  have hVar : ScalarVariation (openCubeSet Q) (fun x => F x - L x) :=
    old_signed_local_removed_variation Q depth nu sigma hnu hsigma k F hF
  have hOrth := scalar_residual_field_orthogonal Q nu sigma hnu hsigma k H
    (fun x => F x - L x) hVar
  have hPairSplit := old_signed_pairing_sub_left Q nu sigma hnu hsigma k hF hL hS
  have horthPair : oldSignedEnergyPairing Q nu sigma k (fun x => F x - L x) S = 0 := by
    simpa [oldSignedEnergyPairing, S, D, F, L, a, scalarCoefficientFlux,
      cube_average_eq_volume_average_open] using hOrth
  have hFL : oldSignedEnergyPairing Q nu sigma k F S =
      oldSignedEnergyPairing Q nu sigma k L S := by
    have := hPairSplit
    rw [horthPair] at this
    linarith
  have hSSource := old_signed_residual_source_pairing Q nu sigma hnu hsigma k hF
  have hConstSource := old_signed_affine_field_const_source Q nu sigma hnu hsigma k P
  rw [hConstSource] at hSSource
  rw [cube_average_eq_volume_average_open] at hSSource
  have hSS : oldSignedEnergyPairing Q nu sigma k S S =
      oldSignedEnergyPairing Q nu sigma k F S := by
    unfold oldSignedEnergyPairing
    simpa [S, F, a, scalarCoefficientFlux] using hSSource
  have hSL : oldSignedEnergyPairing Q nu sigma k S L =
      oldSignedEnergyPairing Q nu sigma k S S := by
    calc
      oldSignedEnergyPairing Q nu sigma k S L =
          oldSignedEnergyPairing Q nu sigma k L S :=
            old_signed_pairing_symm Q nu sigma hnu hsigma k hS hL
      _ = oldSignedEnergyPairing Q nu sigma k F S := hFL.symm
      _ = oldSignedEnergyPairing Q nu sigma k S S := hSS.symm
  have hLS : oldSignedEnergyPairing Q nu sigma k L S =
      oldSignedEnergyPairing Q nu sigma k S S :=
    (old_signed_pairing_symm Q nu sigma hnu hsigma k hL hS).trans hSL
  have hDD : oldSignedEnergyPairing Q nu sigma k D D =
      oldSignedEnergyPairing Q nu sigma k L L -
        oldSignedEnergyPairing Q nu sigma k S S := by
    rw [old_signed_pairing_eq_energyBilin Q nu sigma hnu hsigma k hD hD]
    have hDH : toHilbertBlockL2OfBlockField hD =
        toHilbertBlockL2OfBlockField hS - toHilbertBlockL2OfBlockField hL := by
      exact old_signed_hilbert_sub_field Q hS hL
    rw [hDH]
    have hSH := old_signed_pairing_eq_energyBilin Q nu sigma hnu hsigma k hS hS
    have hLH := old_signed_pairing_eq_energyBilin Q nu sigma hnu hsigma k hL hL
    have hSLH := old_signed_pairing_eq_energyBilin Q nu sigma hnu hsigma k hS hL
    have hLSH := old_signed_pairing_eq_energyBilin Q nu sigma hnu hsigma k hL hS
    let B := scalarFrameRealization Q nu sigma hnu hsigma k
    have hfirst : B.energyBilin
        (toHilbertBlockL2OfBlockField hS - toHilbertBlockL2OfBlockField hL)
        (toHilbertBlockL2OfBlockField hS - toHilbertBlockL2OfBlockField hL) =
        B.energyBilin (toHilbertBlockL2OfBlockField hS)
            (toHilbertBlockL2OfBlockField hS) -
          B.energyBilin (toHilbertBlockL2OfBlockField hS)
            (toHilbertBlockL2OfBlockField hL) -
          B.energyBilin (toHilbertBlockL2OfBlockField hL)
            (toHilbertBlockL2OfBlockField hS) +
          B.energyBilin (toHilbertBlockL2OfBlockField hL)
            (toHilbertBlockL2OfBlockField hL) := by
      calc
        _ = B.energyBilin
              (toHilbertBlockL2OfBlockField hS - toHilbertBlockL2OfBlockField hL)
              (toHilbertBlockL2OfBlockField hS) -
            B.energyBilin
              (toHilbertBlockL2OfBlockField hS - toHilbertBlockL2OfBlockField hL)
              (toHilbertBlockL2OfBlockField hL) := by rw [map_sub]
        _ = _ := by
          rw [B.energySymm
            (toHilbertBlockL2OfBlockField hS - toHilbertBlockL2OfBlockField hL)
            (toHilbertBlockL2OfBlockField hS),
            B.energySymm
              (toHilbertBlockL2OfBlockField hS - toHilbertBlockL2OfBlockField hL)
              (toHilbertBlockL2OfBlockField hL), map_sub, map_sub]
          ring
    rw [hfirst]
    rw [← hSH, ← hLH, ← hSLH, ← hLSH]
    rw [hSL, hLS]
    ring
  have hLocal := old_signed_local_residual_energy Q depth nu sigma hnu hsigma k F F hF hF
  change oldSignedEnergyPairing Q nu sigma k D D = _
  rw [hDD, hLocal]

/-- The actual finite patch energy is the average of the actual affine
coarse energies on its cells.  Each cell term is identified with the
restricted weighted minimizer before its coarse matrix is evaluated. -/
private theorem old_signed_affine_patch_cell_energy (Q : TriadicCube 2)
    (depth : ℕ) (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    oldSignedEnergyPairing Q nu sigma k
      (oldSignedLocalResidual Q depth nu sigma hnu hsigma k
        (fun _ => P) (memLp_const P))
      (oldSignedLocalResidual Q depth nu sigma hnu hsigma k
        (fun _ => P) (memLp_const P)) =
    descendantsAverage Q depth (fun R =>
      blockVecDot P (blockMatVecMul
        (coarseBlockMatrix (openCubeSet R)
          (responseFramePlanarCoefficientField nu sigma k)) P)) := by
  classical
  let a := responseFramePlanarCoefficientField nu sigma k
  let F : Vec 2 → BlockVec 2 := fun _ => P
  let hF : MemBlockL2 (openCubeSet Q) F := memLp_const P
  let L := oldSignedLocalResidual Q depth nu sigma hnu hsigma k F hF
  have hLenergy := old_signed_local_residual_energy Q depth nu sigma hnu hsigma k
    F F hF hF
  have hcell (R : TriadicCube 2) (hR : R ∈ descendantsAtDepth Q depth) :
      volumeAverage (openCubeSet R) (fun x =>
        blockVecDot (L x)
          (blockMatVecMul (blockCoeffField a x) (L x))) =
        blockVecDot P (blockMatVecMul
          (coarseBlockMatrix (openCubeSet R) a) P) := by
    let hRQ := openCubeSet_subset_of_mem_descendantsAtDepth hR
    let kR := oldSignedCellCoefficient Q R hRQ k
    let aR := responseFramePlanarCoefficientField nu sigma kR
    let hFR : MemBlockL2 (openCubeSet R) F :=
      hF.mono_measure (Measure.restrict_mono_set volume hRQ)
    let Z : Vec 2 → BlockVec 2 := oldSignedCellResidual Q R hRQ
      nu sigma hnu hsigma k F hF
    have hRestr := old_signed_local_residual_restrict Q depth nu sigma hnu hsigma k
      F hF R hR
    have hCoeffMat (x : Vec 2) (hx : x ∈ openCubeSet R) : aR x = a x := by
      simp only [aR, a, responseFramePlanarCoefficientField]
      rw [old_signed_cell_coefficient_extension_eq Q R hRQ k hx]
    have hCoeff (x : Vec 2) (hx : x ∈ openCubeSet R) :
        blockCoeffField aR x = blockCoeffField a x := by
      simpa [blockCoeffField] using congrArg blockMatrixOfCoeff (hCoeffMat x hx)
    have hCoeffAE : aR =ᵐ[volume.restrict (openCubeSet R)] a := by
      filter_upwards [ae_restrict_mem (measurableSet_openCubeSet R)] with x hx
      exact hCoeffMat x hx
    have hCoarse := coarseBlockMatrix_congr_of_ae_eq hCoeffAE
    have hRestr' : L =ᵐ[volumeMeasureOn (openCubeSet R)] Z := by
      simpa [L, Z] using hRestr
    have hIntegrand : (fun x => blockVecDot (L x)
        (blockMatVecMul (blockCoeffField a x) (L x))) =ᵐ[
          volumeMeasureOn (openCubeSet R)]
        (fun x => blockVecDot (Z x)
          (blockMatVecMul (blockCoeffField aR x) (Z x))) := by
      filter_upwards [hRestr', ae_restrict_mem (measurableSet_openCubeSet R)]
        with x hLx hx
      rw [hLx, hCoeff x hx]
    have hAverage : volumeAverage (openCubeSet R) (fun x =>
        blockVecDot (L x)
          (blockMatVecMul (blockCoeffField a x) (L x))) =
        volumeAverage (openCubeSet R) (fun x =>
          blockVecDot (Z x)
            (blockMatVecMul (blockCoeffField aR x) (Z x))) := by
      unfold volumeAverage
      congr 1
      exact integral_congr_ae hIntegrand
    have hFRconst : toHilbertBlockL2OfBlockField hFR =
        (scalarFrameRealization R nu sigma hnu hsigma kR).constantField P := by
      have hconst : toHilbertBlockL2OfBlockField hFR =
          blockVecToHilbertBlockL2Const P := by
        apply Lp.ext
        filter_upwards [coeFn_toHilbertBlockL2OfBlockField hFR,
          coeFn_blockVecToHilbertBlockL2Const (U := openCubeSet R) P] with x hx hy
        simpa [F] using hx.trans hy.symm
      exact hconst.trans (by rfl)
    have hZeq : Z = scalarResidualField R nu sigma hnu hsigma kR
        ((scalarFrameRealization R nu sigma hnu hsigma kR).constantField P) := by
      funext x
      change (scalarResidualField R nu sigma hnu hsigma kR
        (toHilbertBlockL2OfBlockField hFR)) x = _
      rw [hFRconst]
    have hAffine := old_signed_affine_energy R nu sigma hnu hsigma kR P
    have hAffineZ : oldSignedEnergyPairing R nu sigma kR Z Z =
        blockVecDot P (blockMatVecMul
          (coarseBlockMatrix (openCubeSet R) aR) P) := by
      simpa [hZeq, aR] using hAffine
    calc
      _ = oldSignedEnergyPairing R nu sigma kR Z Z := by
        simpa [oldSignedEnergyPairing, aR] using hAverage
      _ = blockVecDot P (blockMatVecMul
          (coarseBlockMatrix (openCubeSet R) aR) P) := hAffineZ
      _ = blockVecDot P (blockMatVecMul
          (coarseBlockMatrix (openCubeSet R) a) P) := by rw [hCoarse]
  rw [hLenergy]
  unfold descendantsAverage
  change ((descendantsAtDepth Q depth).card : ℝ)⁻¹ *
      ∑ R ∈ descendantsAtDepth Q depth, volumeAverage (openCubeSet R) (fun x =>
        blockVecDot (L x) (blockMatVecMul (blockCoeffField a x) (L x))) =
    ((descendantsAtDepth Q depth).card : ℝ)⁻¹ *
      ∑ R ∈ descendantsAtDepth Q depth,
        blockVecDot P (blockMatVecMul (coarseBlockMatrix (openCubeSet R) a) P)
  congr 1
  apply Finset.sum_congr rfl
  intro R hR
  exact hcell R hR

private theorem old_signed_descendantsAverage_congr (Q : TriadicCube 2)
    (depth : ℕ) (f g : TriadicCube 2 → ℝ)
    (hfg : ∀ R ∈ descendantsAtDepth Q depth, f R = g R) :
    descendantsAverage Q depth f = descendantsAverage Q depth g := by
  classical
  unfold descendantsAverage
  apply congrArg (fun t => ((descendantsAtDepth Q depth).card : ℝ)⁻¹ * t)
  refine Finset.sum_congr rfl ?_
  intro R hR
  exact hfg R hR

private theorem old_signed_coarse_full_trace_defect (Q : TriadicCube 2)
    (a : CoeffField 2) :
    Homogenization.Book.Ch02.fullBlockTrace
        (toFullBlockMat (coarseBlockMatrix (openCubeSet Q) a)) - 4 =
      traceDefect (openCubeSet Q) a 1 := by
  simp [Homogenization.Book.Ch02.fullBlockTrace, traceDefect, Matrix.trace,
    Matrix.diag_apply, Fintype.sum_sum_type, toFullBlockMat]

/-- At a fixed depth the energy of the actual parent affine corrector is
bounded by the increase in the actual trace defect from the parent to its
cell projections. -/
theorem old_signed_affine_patch_trace_gap_bound (Q : TriadicCube 2)
    (depth : ℕ) (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    oldSignedEnergyPairing Q nu sigma k
      (fun x => scalarResidualField Q nu sigma hnu hsigma k
        ((scalarFrameRealization Q nu sigma hnu hsigma k).constantField P) x -
        oldSignedLocalResidual Q depth nu sigma hnu hsigma k (fun _ => P)
          (memLp_const P) x)
      (fun x => scalarResidualField Q nu sigma hnu hsigma k
        ((scalarFrameRealization Q nu sigma hnu hsigma k).constantField P) x -
        oldSignedLocalResidual Q depth nu sigma hnu hsigma k (fun _ => P)
          (memLp_const P) x) ≤
    (descendantsAverage Q depth (fun R =>
      traceDefect (openCubeSet R) (responseFramePlanarCoefficientField nu sigma k) 1) -
        traceDefect (openCubeSet Q) (responseFramePlanarCoefficientField nu sigma k) 1) *
        blockVecDot P P := by
  classical
  let a := responseFramePlanarCoefficientField nu sigma k
  let A := coarseBlockMatrix (openCubeSet Q) a
  let B := descendantsAverageBlockMat Q depth (fun R =>
    coarseBlockMatrix (openCubeSet R) a)
  let M : FullBlockMat 2 := toFullBlockMat B - toFullBlockMat A
  let D : Vec 2 → BlockVec 2 := fun x =>
    scalarResidualField Q nu sigma hnu hsigma k
      ((scalarFrameRealization Q nu sigma hnu hsigma k).constantField P) x -
    oldSignedLocalResidual Q depth nu sigma hnu hsigma k (fun _ => P)
      (memLp_const P) x
  have hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) nu sigma hnu hsigma k
  have hPatch := old_signed_affine_patch_energy_identity Q depth nu sigma
    hnu hsigma k P
  have hLocal := old_signed_local_residual_energy Q depth nu sigma hnu hsigma k
    (fun _ => P) (fun _ => P) (memLp_const P) (memLp_const P)
  have hCell := old_signed_affine_patch_cell_energy Q depth nu sigma
    hnu hsigma k P
  have hParent := old_signed_affine_energy Q nu sigma hnu hsigma k P
  have hAvg := blockVecDot_blockMatVecMul_descendantsAverageBlockMat Q depth
    (fun R => coarseBlockMatrix (openCubeSet R) a) P P
  have hgap : oldSignedEnergyPairing Q nu sigma k D D =
      blockVecDot P (blockMatVecMul (ofFullBlockMat M) P) := by
    calc
      oldSignedEnergyPairing Q nu sigma k D D =
          descendantsAverage Q depth (fun R => volumeAverage (openCubeSet R) (fun x =>
            blockVecDot (oldSignedLocalResidual Q depth nu sigma hnu hsigma k
                (fun _ => P) (memLp_const P) x)
              (blockMatVecMul (blockCoeffField a x)
                (oldSignedLocalResidual Q depth nu sigma hnu hsigma k
                  (fun _ => P) (memLp_const P) x)))) -
            oldSignedEnergyPairing Q nu sigma k
              (scalarResidualField Q nu sigma hnu hsigma k
                ((scalarFrameRealization Q nu sigma hnu hsigma k).constantField P))
              (scalarResidualField Q nu sigma hnu hsigma k
                ((scalarFrameRealization Q nu sigma hnu hsigma k).constantField P)) := by
              simpa [D, a] using hPatch
      _ = descendantsAverage Q depth (fun R =>
            blockVecDot P (blockMatVecMul
              (coarseBlockMatrix (openCubeSet R) a) P)) -
            blockVecDot P (blockMatVecMul A P) := by
              rw [← hLocal, hCell, hParent]
      _ = blockVecDot P (blockMatVecMul (ofFullBlockMat M) P) := by
              rw [← hAvg]
              exact blockVecDot_blockMatVecMul_sub_eq_ofFullBlockMat_sub B A P
  have hSub : BlockMatLoewnerLE A B := by
    exact cube_coarse_matrix_subadditive Q depth a hEll
  have hAsymm : IsSymmetricBlockMat A := Variational.coarseBlockMatrix_symmetric _ _
  have hBsymm : IsSymmetricBlockMat B := by
    intro α β
    cases α with
    | inl i =>
        cases β with
        | inl j =>
            change descendantsAverage Q depth (fun R =>
              (coarseBlockMatrix (openCubeSet R) a).upperLeft i j) =
              descendantsAverage Q depth (fun R =>
                (coarseBlockMatrix (openCubeSet R) a).upperLeft j i)
            apply old_signed_descendantsAverage_congr
            intro R hR
            exact Variational.coarseBlockMatrix_symmetric _ _ (Sum.inl i) (Sum.inl j)
        | inr j =>
            change descendantsAverage Q depth (fun R =>
              (coarseBlockMatrix (openCubeSet R) a).upperRight i j) =
              descendantsAverage Q depth (fun R =>
                (coarseBlockMatrix (openCubeSet R) a).lowerLeft j i)
            apply old_signed_descendantsAverage_congr
            intro R hR
            exact Variational.coarseBlockMatrix_symmetric _ _ (Sum.inl i) (Sum.inr j)
    | inr i =>
        cases β with
        | inl j =>
            change descendantsAverage Q depth (fun R =>
              (coarseBlockMatrix (openCubeSet R) a).lowerLeft i j) =
              descendantsAverage Q depth (fun R =>
                (coarseBlockMatrix (openCubeSet R) a).upperRight j i)
            apply old_signed_descendantsAverage_congr
            intro R hR
            exact Variational.coarseBlockMatrix_symmetric _ _ (Sum.inr i) (Sum.inl j)
        | inr j =>
            change descendantsAverage Q depth (fun R =>
              (coarseBlockMatrix (openCubeSet R) a).lowerRight i j) =
              descendantsAverage Q depth (fun R =>
                (coarseBlockMatrix (openCubeSet R) a).lowerRight j i)
            apply old_signed_descendantsAverage_congr
            intro R hR
            exact Variational.coarseBlockMatrix_symmetric _ _ (Sum.inr i) (Sum.inr j)
  have hPSD : M.PosSemidef := by
    dsimp [M]
    exact Homogenization.Book.Ch05.Section56.blockSub_posSemidef_of_blockMatLoewnerLE
      hSub hAsymm hBsymm
  have hNormTrace :
      ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) M‖ ≤
        Homogenization.Book.Ch02.fullBlockTrace M :=
    Homogenization.Book.Ch05.Section56.fullBlockOperatorNorm_le_trace_of_posSemidef M hPSD
  have hTraceParent := old_signed_coarse_full_trace_defect Q a
  have hTraceCell (R : TriadicCube 2) :
      Matrix.trace (coarseBlockMatrix (openCubeSet R) a).upperLeft +
        Matrix.trace (coarseBlockMatrix (openCubeSet R) a).lowerRight =
      traceDefect (openCubeSet R) a 1 + 4 := by
    have hFull : Homogenization.Book.Ch02.fullBlockTrace
        (toFullBlockMat (coarseBlockMatrix (openCubeSet R) a)) =
        Matrix.trace (coarseBlockMatrix (openCubeSet R) a).upperLeft +
          Matrix.trace (coarseBlockMatrix (openCubeSet R) a).lowerRight := by
      simp [Homogenization.Book.Ch02.fullBlockTrace, Matrix.trace,
        Matrix.diag_apply, Fintype.sum_sum_type, toFullBlockMat]
    have hDefect := old_signed_coarse_full_trace_defect R a
    linarith
  have hBlockTrace : Homogenization.Book.Ch02.fullBlockTrace (toFullBlockMat B) =
      descendantsAverage Q depth (fun R =>
        Matrix.trace (coarseBlockMatrix (openCubeSet R) a).upperLeft +
          Matrix.trace (coarseBlockMatrix (openCubeSet R) a).lowerRight) := by
    have hUpper : Matrix.trace B.upperLeft = descendantsAverage Q depth (fun R =>
        Matrix.trace (coarseBlockMatrix (openCubeSet R) a).upperLeft) := by
      simp only [Matrix.trace, Fin.sum_univ_two, Matrix.diag_apply,
        B, descendantsAverageBlockMat, descendantsAverageMat]
      exact (descendantsAverage_add Q depth
        (fun R => (coarseBlockMatrix (openCubeSet R) a).upperLeft 0 0)
        (fun R => (coarseBlockMatrix (openCubeSet R) a).upperLeft 1 1)).symm
    have hLower : Matrix.trace B.lowerRight = descendantsAverage Q depth (fun R =>
        Matrix.trace (coarseBlockMatrix (openCubeSet R) a).lowerRight) := by
      simp only [Matrix.trace, Fin.sum_univ_two, Matrix.diag_apply,
        B, descendantsAverageBlockMat, descendantsAverageMat]
      exact (descendantsAverage_add Q depth
        (fun R => (coarseBlockMatrix (openCubeSet R) a).lowerRight 0 0)
        (fun R => (coarseBlockMatrix (openCubeSet R) a).lowerRight 1 1)).symm
    calc
      Homogenization.Book.Ch02.fullBlockTrace (toFullBlockMat B) =
          Matrix.trace B.upperLeft + Matrix.trace B.lowerRight := by
            simp [Homogenization.Book.Ch02.fullBlockTrace, Matrix.trace,
              Fintype.sum_sum_type, toFullBlockMat]
      _ = _ := by rw [hUpper, hLower, descendantsAverage_add]
  have hTraceAverage : Homogenization.Book.Ch02.fullBlockTrace (toFullBlockMat B) - 4 =
      descendantsAverage Q depth (fun R => traceDefect (openCubeSet R) a 1) := by
    rw [hBlockTrace]
    have hReplace := old_signed_descendantsAverage_congr Q depth
      (fun R => Matrix.trace (coarseBlockMatrix (openCubeSet R) a).upperLeft +
        Matrix.trace (coarseBlockMatrix (openCubeSet R) a).lowerRight)
      (fun R => traceDefect (openCubeSet R) a 1 + 4)
      (fun R _ => hTraceCell R)
    rw [hReplace, descendantsAverage_add, descendantsAverage_const]
    simp [descendantsAverage]
  have hTraceDiff : Homogenization.Book.Ch02.fullBlockTrace M =
      Homogenization.Book.Ch02.fullBlockTrace (toFullBlockMat B) -
        Homogenization.Book.Ch02.fullBlockTrace (toFullBlockMat A) := by
    simp [M, Homogenization.Book.Ch02.fullBlockTrace, Finset.sum_sub_distrib]
  have hTraceGap : Homogenization.Book.Ch02.fullBlockTrace M =
      descendantsAverage Q depth (fun R => traceDefect (openCubeSet R) a 1) -
        traceDefect (openCubeSet Q) a 1 := by
    rw [hTraceDiff]
    have hTraceB : Homogenization.Book.Ch02.fullBlockTrace (toFullBlockMat B) =
        descendantsAverage Q depth (fun R => traceDefect (openCubeSet R) a 1) + 4 := by
      linarith [hTraceAverage]
    have hTraceA : Homogenization.Book.Ch02.fullBlockTrace (toFullBlockMat A) =
        traceDefect (openCubeSet Q) a 1 + 4 := by
      linarith [hTraceParent]
    rw [hTraceB, hTraceA]
    ring
  have hquadEq : ASDExplicitGamma.Inverse.fullMatrixQuadratic
        (toFullBlockVec P) M = blockVecDot P (blockMatVecMul (ofFullBlockMat M) P) := by
    have h := ASDExplicitGamma.Inverse.fullMatrixQuadratic_block (ofFullBlockMat M) P
    simpa using h
  have hquad := ASDExplicitGamma.Inverse.full_matrix_quadratic_abs_le_euclidean_opNorm
    M (toFullBlockVec P)
  rw [hquadEq, dotProduct_toFullBlockVec] at hquad
  have hP : 0 ≤ blockVecDot P P := blockVecDot_nonneg P
  calc
    oldSignedEnergyPairing Q nu sigma k D D =
        blockVecDot P (blockMatVecMul (ofFullBlockMat M) P) := hgap
    _ ≤ |blockVecDot P (blockMatVecMul (ofFullBlockMat M) P)| := le_abs_self _
    _ ≤ ‖Matrix.toEuclideanCLM (n := BlockCoord 2) (𝕜 := ℝ) M‖ *
          blockVecDot P P := hquad
    _ ≤ Homogenization.Book.Ch02.fullBlockTrace M * blockVecDot P P :=
      mul_le_mul_of_nonneg_right hNormTrace hP
    _ = (descendantsAverage Q depth (fun R => traceDefect (openCubeSet R) a 1) -
          traceDefect (openCubeSet Q) a 1) * blockVecDot P P := by rw [hTraceGap]

/-- The depth-j potential projections of the actual affine corrector error are
controlled by the inverse maximum at depth j times the trace increment from
the parent to its cell minimizers. -/
theorem old_signed_affine_first_projection_bound (Q : TriadicCube 2)
    (depth : ℕ) (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    (∑ i, energy Q (cubeProjection Q depth (fun x =>
      (scalarResidualField Q nu sigma hnu hsigma k
        ((scalarFrameRealization Q nu sigma hnu hsigma k).constantField P) x).1 i - P.1 i))) ≤
      lemmaVInverseDepthMax Q (responseFramePlanarCoefficientField nu sigma k) depth *
        (descendantsAverage Q depth (fun R => traceDefect (openCubeSet R)
          (responseFramePlanarCoefficientField nu sigma k) 1) -
          traceDefect (openCubeSet Q) (responseFramePlanarCoefficientField nu sigma k) 1) *
        blockVecDot P P := by
  classical
  let a := responseFramePlanarCoefficientField nu sigma k
  let S : Vec 2 → BlockVec 2 := scalarResidualField Q nu sigma hnu hsigma k
    ((scalarFrameRealization Q nu sigma hnu hsigma k).constantField P)
  let L : Vec 2 → BlockVec 2 := oldSignedLocalResidual Q depth nu sigma hnu hsigma k
    (fun _ => P) (memLp_const P)
  let D : Vec 2 → BlockVec 2 := fun x => S x - L x
  have hS : MemBlockL2 (openCubeSet Q) S := Lp.memLp _
  have hL : MemBlockL2 (openCubeSet Q) L :=
    old_signed_local_residual_memLp Q depth nu sigma hnu hsigma k
      (fun _ => P) (memLp_const P)
  have hD : MemBlockL2 (openCubeSet Q) D := hS.sub hL
  have hParentVar := old_signed_affine_removed_variation Q nu sigma hnu hsigma k P
  have hLocalVar := old_signed_local_removed_variation Q depth nu sigma hnu hsigma k
    (fun _ => P) (memLp_const P)
  have hDVar : ScalarVariation (openCubeSet Q) D := by
    have hsum := scalar_variation_add hLocalVar
      (scalar_variation_smul hParentVar (-1 : ℝ))
    have hsum' : ScalarVariation (openCubeSet Q)
        ((fun x => P - L x) + (-1 : ℝ) • (fun x => P - S x)) := by
      exact hsum
    have hfields : ((fun x => P - L x) + (-1 : ℝ) • (fun x => P - S x)) = D := by
      funext x
      simp only [Pi.add_apply, Pi.smul_apply, D]
      apply Prod.ext <;> funext i <;> simp
    exact old_signed_scalar_variation_congr_ae
      (ae_of_all (volumeMeasureOn (openCubeSet Q)) fun x => congrFun hfields x) hsum'
  have hCompat := scalar_variation_compatible hDVar
  let W : BlockState 2 := ⟨fun x => (D x).1, fun x => (D x).2⟩
  have hWpot : IsBlockPotentialOn (openCubeSet Q) W := hCompat.2.1
  have hWsol : IsBlockSolenoidalOn (openCubeSet Q) W := hCompat.2.2
  have hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) nu sigma hnu hsigma k
  have hProjD := compatible_projectionEnergy_bound hEll W hWpot hWsol hD depth
  have hScoord (i : Fin 2) : MemLp (fun x => (S x).1 i) 2
      (normalizedCubeMeasure Q) :=
    memLp_normalized_of_memL2On
      (memScalarL2_coord_of_memVectorL2 (memVectorL2_fst_of_memBlockL2 hS) i)
  have hLcoordParent (i : Fin 2) : MemLp (fun x => (L x).1 i) 2
      (normalizedCubeMeasure Q) :=
    memLp_normalized_of_memL2On
      (memScalarL2_coord_of_memVectorL2 (memVectorL2_fst_of_memBlockL2 hL) i)
  have hPcoord (i : Fin 2) : MemLp (fun _ : Vec 2 => P.1 i) 2
      (normalizedCubeMeasure Q) := memLp_const (P.1 i)
  have hSPcoord (i : Fin 2) : MemLp (fun x => (S x).1 i - P.1 i) 2
      (normalizedCubeMeasure Q) := (hScoord i).sub (hPcoord i)
  have hPLcoord (i : Fin 2) : MemLp (fun x => P.1 i - (L x).1 i) 2
      (normalizedCubeMeasure Q) := (hPcoord i).sub (hLcoordParent i)
  have hLocalMean (i : Fin 2) (R : TriadicCube 2)
      (hR : R ∈ descendantsAtDepth Q depth) :
      cubeAverage R (fun x => (L x).1 i) = P.1 i :=
    old_signed_local_first_mean Q depth nu sigma hnu hsigma k P R hR i
  have hPLproj (i : Fin 2) :
      cubeProjection Q depth (fun x => P.1 i - (L x).1 i) = 0 := by
    funext x
    by_cases hx : x ∈ cubeSet Q
    · obtain ⟨R, hR, hxR⟩ := exists_mem_descendantsAtDepth_of_mem_cubeSet depth hx
      rw [cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth _ hR hxR]
      have hLR : MemBlockL2 (openCubeSet R) L := by
        exact hL.mono_measure (Measure.restrict_mono_set volume
          (openCubeSet_subset_of_mem_descendantsAtDepth hR))
      have hLcoord (i : Fin 2) : MemLp (fun y => (L y).1 i) 2
          (normalizedCubeMeasure R) :=
        memLp_normalized_of_memL2On
          (memScalarL2_coord_of_memVectorL2 (memVectorL2_fst_of_memBlockL2 hLR) i)
      have hconst : MemLp (fun _ : Vec 2 => P.1 i) 2
          (normalizedCubeMeasure R) := memLp_const (P.1 i)
      calc
        cubeAverage R (fun y => P.1 i - (L y).1 i) =
            cubeAverage R (fun _ => P.1 i) - cubeAverage R (fun y => (L y).1 i) :=
          old_signed_cubeAverage_sub R hconst (hLcoord i)
        _ = 0 := by rw [cubeAverage_const, hLocalMean i R hR, sub_self]
    · exact cubeProjection_eq_zero_of_not_mem_cubeSet Q depth _ hx
  have hProjAdd (i : Fin 2) :
      cubeProjection Q depth (fun x => (D x).1 i) =
        fun x => cubeProjection Q depth (fun y => (S y).1 i - P.1 i) x := by
    have hdecomp : (fun x => (D x).1 i) =
        (fun x => (S x).1 i - P.1 i) + (fun x => P.1 i - (L x).1 i) := by
      funext x
      simp only [D]
      change (S x).1 i - (L x).1 i =
        ((S x).1 i - P.1 i) + (P.1 i - (L x).1 i)
      ring
    calc
      cubeProjection Q depth (fun x => (D x).1 i) =
          cubeProjection Q depth
            ((fun x => (S x).1 i - P.1 i) + (fun x => P.1 i - (L x).1 i)) := by
              rw [hdecomp]
      _ = cubeProjection Q depth (fun x => (S x).1 i - P.1 i) +
            cubeProjection Q depth (fun x => P.1 i - (L x).1 i) :=
              projection_add Q depth (hSPcoord i) (hPLcoord i)
      _ = fun x => cubeProjection Q depth (fun y => (S y).1 i - P.1 i) x := by
            rw [hPLproj i]
            simp
  have hProjEnergyEq :
      (∑ i, energy Q (cubeProjection Q depth (fun x =>
        (scalarResidualField Q nu sigma hnu hsigma k
          ((scalarFrameRealization Q nu sigma hnu hsigma k).constantField P) x).1 i - P.1 i))) =
      ∑ i, energy Q (cubeProjection Q depth (fun x => (D x).1 i)) := by
    apply Finset.sum_congr rfl
    intro i hi
    simpa [S] using (congrArg (energy Q) (hProjAdd i)).symm
  have hAverage : cubeAverage Q (blockPairingIntegrand a W W) =
      oldSignedEnergyPairing Q nu sigma k D D := by
    rw [cubeAverage_eq_integralAverage_openCubeSet Q]
    rfl
  have hPatchGap := old_signed_affine_patch_trace_gap_bound Q depth nu sigma
    hnu hsigma k P
  have hMnonneg := lemmaVInverseDepthMax_nonneg Q a depth
  calc
    _ = ∑ i, energy Q (cubeProjection Q depth (fun x => (D x).1 i)) := hProjEnergyEq
    _ ≤ lemmaVInverseDepthMax Q a depth * cubeAverage Q (blockPairingIntegrand a W W) := hProjD
    _ = lemmaVInverseDepthMax Q a depth * oldSignedEnergyPairing Q nu sigma k D D := by
      rw [hAverage]
    _ ≤ lemmaVInverseDepthMax Q a depth *
        ((descendantsAverage Q depth (fun R => traceDefect (openCubeSet R) a 1) -
          traceDefect (openCubeSet Q) a 1) * blockVecDot P P) :=
      mul_le_mul_of_nonneg_left hPatchGap hMnonneg
    _ = lemmaVInverseDepthMax Q a depth *
        (descendantsAverage Q depth (fun R => traceDefect (openCubeSet R) a 1) -
          traceDefect (openCubeSet Q) a 1) * blockVecDot P P := by ring

private theorem old_signed_trace_history_toReal' (Q : TriadicCube 2)
    (a : CoeffField 2) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) :
    Inverse.rawWeakTraceHistory (fun j => descendantsAverage Q j
      (fun R => traceDefect (openCubeSet R) a 1)) =
      (oldSignedTraceHistory Q a).toReal := by
  let α := Scalar.inverseHistoryDiscount
  let d (j : ℕ) := descendantsAverage Q j
    (fun R => traceDefect (openCubeSet R) a 1)
  have hα : 0 ≤ α := Scalar.inverse_history_discount_range.1.le
  have h1α : 0 ≤ 1 - α := sub_nonneg.mpr Scalar.inverse_history_discount_range.2.le
  have hTrace : Summable (fun j : ℕ => α ^ j * d j) := by
    simpa [α, d] using old_signed_trace_depth_series_summable Q a hEll
  have hTerm (j : ℕ) : 0 ≤ α ^ j * d j := by
    have hEllR (R : TriadicCube 2) (hR : R ∈ descendantsAtDepth Q j) :
        IsEllipticFieldOn lam Lam (openCubeSet R) a :=
      hEll.mono (measurableSet_openCubeSet R)
        (openCubeSet_subset_of_mem_descendantsAtDepth hR)
    have hD : 0 ≤ d j := by
      apply descendantsAverage_nonneg Q j _
      intro R hR
      exact ASDExplicitGamma.Cold.coarse_square_traceDefect_nonneg R (hEllR R hR)
    exact mul_nonneg (pow_nonneg hα j) hD
  have hSumNonneg : 0 ≤ ∑' j : ℕ, α ^ j * d j := tsum_nonneg hTerm
  have hSeriesENN : (∑' j : ℕ, ENNReal.ofReal (α ^ j * d j)) =
      ENNReal.ofReal (∑' j : ℕ, α ^ j * d j) :=
    (ENNReal.ofReal_tsum_of_nonneg hTerm hTrace).symm
  have hHistoryENN : oldSignedTraceHistory Q a =
      ENNReal.ofReal ((1 - α) * ∑' j : ℕ, α ^ j * d j) := by
    unfold oldSignedTraceHistory
    rw [hSeriesENN]
    rw [← ENNReal.ofReal_mul h1α]
  unfold Inverse.rawWeakTraceHistory
  rw [hHistoryENN, ENNReal.toReal_ofReal (mul_nonneg h1α hSumNonneg)]

/-- The actual affine first-block corrector is bounded by the product of the
OLD response and trace histories, with the exact source factor `1 + α`. -/
theorem old_signed_affine_first_corrector (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    (vectorWeakHaarNorm Q (fun x =>
      (scalarResidualField Q nu sigma hnu hsigma k
        ((scalarFrameRealization Q nu sigma hnu hsigma k).constantField P) x).1 - P.1)) ^ 2 ≤
      oldSignedCorrectorHistory Q (responseFramePlanarCoefficientField nu sigma k) *
        blockVecDot P P := by
  classical
  let α := Scalar.inverseHistoryDiscount
  let a := responseFramePlanarCoefficientField nu sigma k
  let H := (scalarFrameRealization Q nu sigma hnu hsigma k).constantField P
  let S : Vec 2 → BlockVec 2 := scalarResidualField Q nu sigma hnu hsigma k H
  let b (j : ℕ) := lemmaVInverseDepthMax Q a j
  let d (j : ℕ) := descendantsAverage Q j
    (fun R => traceDefect (openCubeSet R) a 1)
  let e (j : ℕ) := ∑ i, energy Q (cubeProjection Q j
    (fun x => (S x).1 i - P.1 i))
  let F : Vec 2 → Fin 2 → ℝ := fun x i => (S x).1 i - P.1 i
  let p := blockVecDot P P
  have hEll := responseFramePlanarCoefficientField_isElliptic
    (measurableSet_openCubeSet Q) nu sigma hnu hsigma k
  have hS : MemBlockL2 (openCubeSet Q) S := Lp.memLp _
  have hFcoord (i : Fin 2) : MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q) := by
    have hScoord : MemLp (fun x => (S x).1 i) 2 (normalizedCubeMeasure Q) :=
      memLp_normalized_of_memL2On
        (memScalarL2_coord_of_memVectorL2 (memVectorL2_fst_of_memBlockL2 hS) i)
    exact hScoord.sub (memLp_const (P.1 i))
  have hq : (1 : ℝ) < Real.sqrt 3 := by
    have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg (3 : ℝ)]
  have hBaseSq : Scalar.sourceHaarBase ^ 2 = Real.sqrt 3 := by
    rw [Scalar.sourceHaarBase, Real.sqrt_eq_rpow,
      ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    norm_num
  have hBaseInv : Scalar.sourceHaarBase⁻¹ = α := by
    dsimp [α]
    exact Scalar.inverse_history_discount_eq.symm
  have hInvSqrt : (Real.sqrt 3)⁻¹ = α ^ 2 := by
    have h := congrArg (fun x : ℝ => x⁻¹) hBaseSq
    rw [← inv_pow, hBaseInv] at h
    exact h.symm
  have hCoordSummable (i : Fin 2) : Summable (fun j : ℕ =>
      ((Real.sqrt 3)⁻¹) ^ j * energy Q (cubeProjection Q j (fun x => F x i))) :=
    summable_weighted_projections Q hq (hFcoord i)
  have hAlphaCoordSummable (i : Fin 2) : Summable (fun j : ℕ =>
      α ^ (2 * j) * energy Q (cubeProjection Q j (fun x => F x i))) := by
    simpa only [hInvSqrt, ← pow_mul] using hCoordSummable i
  have hEnergySummable : Summable (fun j : ℕ => α ^ (2 * j) * e j) := by
    simp_rw [e, Finset.mul_sum]
    exact summable_sum fun i hi => hAlphaCoordSummable i
  have hEnergy : vectorWeakHaarEnergy Q F =
      (1 - α ^ 2) * ∑' j : ℕ, α ^ (2 * j) * e j := by
    have hRep : vectorWeakHaarEnergy Q F =
        (1 - (Real.sqrt 3)⁻¹) * ∑' j : ℕ,
          ((Real.sqrt 3)⁻¹) ^ j * (∑ i, energy Q (cubeProjection Q j (fun x => F x i))) := by
      simp_rw [vectorWeakHaarEnergy, dualEnergy_eq Q hq (hFcoord _)]
      rw [← Finset.mul_sum,
        ← Summable.tsum_finsetSum (fun i _ => hCoordSummable i)]
      congr 1
      exact tsum_congr fun j => (Finset.mul_sum _ _ _).symm
    rw [hRep, hInvSqrt]
    congr 1
    apply tsum_congr
    intro j
    have hpow : (α ^ 2) ^ j = α ^ (2 * j) := by rw [← pow_mul]
    rw [hpow]
  have hParentNonneg : 0 ≤ traceDefect (openCubeSet Q) a 1 :=
    ASDExplicitGamma.Cold.coarse_square_traceDefect_nonneg Q hEll
  have hP : 0 ≤ p := by exact blockVecDot_nonneg P
  have hα : 0 ≤ α := Scalar.inverse_history_discount_range.1.le
  have hαlt : α < 1 := Scalar.inverse_history_discount_range.2
  have hα2 : 0 ≤ 1 - α ^ 2 := by
    apply sub_nonneg.mpr
    exact (pow_le_one₀ hα hαlt.le)
  have hTnonneg : ∀ j, 0 ≤ d j := by
    intro j
    apply descendantsAverage_nonneg Q j _
    intro R hR
    have hEllR := hEll.mono (measurableSet_openCubeSet R)
      (openCubeSet_subset_of_mem_descendantsAtDepth hR)
    exact ASDExplicitGamma.Cold.coarse_square_traceDefect_nonneg R hEllR
  have hTsum : Summable (fun j : ℕ => α ^ j * d j) := by
    simpa [α, d] using old_signed_trace_depth_series_summable Q a hEll
  have hdepth (j : ℕ) : α ^ j * b j ≤ oldSignedInverseHistory Q a := by
    have h := Inverse.actual_inverse_depth_discount_bound Q a hEll 1 (by norm_num) j
    simpa [α, b, oldSignedInverseHistory] using h
  have hProxySummable : Summable (fun j : ℕ => α ^ (2 * j) * b j * d j) := by
    apply Summable.of_nonneg_of_le
    · intro j
      have hαj : 0 ≤ α ^ (2 * j) := pow_nonneg hα _
      have hb : 0 ≤ b j := lemmaVInverseDepthMax_nonneg Q a j
      exact mul_nonneg (mul_nonneg hαj hb) (hTnonneg j)
    · intro j
      have hweight : α ^ (2 * j) * b j * d j ≤
          oldSignedInverseHistory Q a * (α ^ j * d j) := by
        calc
          α ^ (2 * j) * b j * d j = (α ^ j * b j) * (α ^ j * d j) := by
            rw [show 2 * j = j + j by omega, pow_add]
            ring
          _ ≤ oldSignedInverseHistory Q a * (α ^ j * d j) :=
            mul_le_mul_of_nonneg_right (hdepth j)
              (mul_nonneg (pow_nonneg hα j) (hTnonneg j))
      exact hweight
    · exact hTsum.mul_left (oldSignedInverseHistory Q a)
  have hProj (j : ℕ) : e j ≤ b j * d j * p := by
    have hGap := old_signed_affine_first_projection_bound Q j nu sigma
      hnu hsigma k P
    calc
      e j ≤ b j * (d j - traceDefect (openCubeSet Q) a 1) * p := by
        simpa [e, b, d, a] using hGap
      _ ≤ b j * d j * p := by
        have hcoef : 0 ≤ b j * p := mul_nonneg
          (lemmaVInverseDepthMax_nonneg Q a j) hP
        calc
          b j * (d j - traceDefect (openCubeSet Q) a 1) * p =
              (b j * p) * (d j - traceDefect (openCubeSet Q) a 1) := by ring
          _ ≤ (b j * p) * d j := mul_le_mul_of_nonneg_left
            (by linarith) hcoef
          _ = b j * d j * p := by ring
  have hProxyP : Summable (fun j : ℕ => α ^ (2 * j) * b j * d j * p) :=
    hProxySummable.mul_right p
  have hWeakProxy : vectorWeakHaarEnergy Q F ≤
      Inverse.rawWeakTraceProxy b d * p := by
    have hterm (j : ℕ) : α ^ (2 * j) * e j ≤
        α ^ (2 * j) * b j * d j * p := by
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left
        (hProj j) (pow_nonneg hα (2 * j))
    calc
      vectorWeakHaarEnergy Q F =
          (1 - α ^ 2) * ∑' j : ℕ, α ^ (2 * j) * e j := hEnergy
      _ ≤ (1 - α ^ 2) * ∑' j : ℕ, α ^ (2 * j) * b j * d j * p :=
        mul_le_mul_of_nonneg_left (hEnergySummable.tsum_le_tsum hterm hProxyP) hα2
      _ = Inverse.rawWeakTraceProxy b d * p := by
        unfold Inverse.rawWeakTraceProxy
        rw [tsum_mul_right]
        simp only [α]
        ring
  have hTraceHistory : Inverse.rawWeakTraceHistory d =
      (oldSignedTraceHistory Q a).toReal :=
    old_signed_trace_history_toReal' Q a hEll
  have hRaw := Inverse.raw_weak_trace_proxy_le b d (oldSignedInverseHistory Q a)
    hdepth hTnonneg hProxySummable hTsum
  have hBM := old_signed_inverse_history_le_response_history Q a hEll
  have hTraceNonneg : 0 ≤ (oldSignedTraceHistory Q a).toReal := by positivity
  calc
    (vectorWeakHaarNorm Q F) ^ 2 = vectorWeakHaarEnergy Q F := by
      rw [vectorWeakHaarNorm]
      exact Real.sq_sqrt (vectorWeakHaarEnergy_nonneg Q F)
    _ ≤ Inverse.rawWeakTraceProxy b d * p := hWeakProxy
    _ ≤ ((1 + α) * oldSignedInverseHistory Q a *
        Inverse.rawWeakTraceHistory d) * p :=
      mul_le_mul_of_nonneg_right hRaw hP
    _ = (1 + α) * oldSignedInverseHistory Q a *
        (oldSignedTraceHistory Q a).toReal * p := by rw [hTraceHistory]
    _ ≤ (1 + α) * oldSignedResponseHistory Q a *
        (oldSignedTraceHistory Q a).toReal * p := by
      have hfactor : 0 ≤ (1 + α) * (oldSignedTraceHistory Q a).toReal :=
        mul_nonneg (by linarith) hTraceNonneg
      calc
        _ = oldSignedInverseHistory Q a *
            ((1 + α) * (oldSignedTraceHistory Q a).toReal) * p := by ring
        _ ≤ oldSignedResponseHistory Q a *
            ((1 + α) * (oldSignedTraceHistory Q a).toReal) * p :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBM hfactor) hP
        _ = _ := by ring
    _ = oldSignedCorrectorHistory Q a * p := by
      rw [oldSignedCorrectorHistory]
    _ = _ := by rfl

end ASDExplicitGamma.Native
