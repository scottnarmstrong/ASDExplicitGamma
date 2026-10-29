module

public import ASDExplicitGamma.Native.OldSignedCanonicalTrialAssembly
public import ASDExplicitGamma.Native.OldSignedActualHessianTrial
public import ASDExplicitGamma.Native.OldSignedTrialCandidates
public import ASDExplicitGamma.Native.OldSignedActualTrialExpansion
public import ASDExplicitGamma.Main.HotPatchSource

/-! Hot-patch trial, package B (trial): the signed trial expansion made generic
in the localized source field. The original OLD trial and the hot-patched trial
are two instances. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open Homogenization MeasureTheory Response Scalar Gaussian Main Triadic
open ASDExplicitGamma.Response ASDExplicitGamma.Scalar ASDExplicitGamma.Gaussian

noncomputable section

/-- The nine signed trial families for an arbitrary localized source field
`H n P` (the doubled source for mode `n` and load `P`). -/
def oldSignedGenericTrialTerms (Q : TriadicCube 2) (depth : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l})
    (H : whiteBasisIndex → BlockVec 2 → Vec 2 → BlockVec 2)
    (hH : ∀ n P, MemBlockL2 (openCubeSet Q) (H n P)) : OldSignedTrialTerms :=
  let E := oldSignedEnergyPairing Q nu sigma k
  let C := fun n => oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
  let S := fun P => oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P
  let Z := fun plus n i => oldSignedPatchedFlat Q depth nu sigma hnu hsigma k b L plus n i
  let R := fun n P => oldSignedLocalResidual Q depth nu sigma hnu hsigma k (H n P) (hH n P)
  let F := fun plus n i => oldSignedFlatInput Q b L plus n i
  { flat := fun n => (∑ i : Fin 2, E (Z true n i) (Z true n i)) +
      (∑ i : Fin 2, E (Z false n i) (Z false n i)) - 2 * oldSignedFlatDirichletModeEnergy Q b L n
    source := fun n => ∑ c : BlockCoord 2, E (R n (blockBasis c)) (R n (blockBasis c))
    mixedPlus := fun n => ∑ i : Fin 2, (E (Z true n i) (R n (oldSignedFlatLoad true i)) -
      volumeAverage (openCubeSet Q) (fun x =>
        vecDot (F true n i x).2 (H n (oldSignedFlatLoad true i) x).2))
    mixedMinus := fun n => ∑ i : Fin 2, (E (Z false n i) (R n (oldSignedFlatLoad false i)) -
      volumeAverage (openCubeSet Q) (fun x =>
        vecDot (F false n i x).2 (H n (oldSignedFlatLoad false i) x).2))
    feedbackPlus := fun n => ∑ i : Fin 2, E (S (blockBasis (Sum.inl i))) (C n (Z true n i))
    feedbackSource := fun n => ∑ c : BlockCoord 2, E (S (blockBasis c)) (C n (R n (blockBasis c)))
    feedbackMinus := fun n => (∑ i : Fin 2, E (S (blockBasis (Sum.inr i))) (C n (Z false n i))) -
      ∑ i : Fin 2, E (S (blockBasis (Sum.inr i))) (C n (F false n i))
    covarianceTop := fun n => 2 * ∑ i : Fin 2, volumeAverage (openCubeSet Q) (fun x =>
      vecDot (oldSignedFlatPlusBlock Q b L n i x).2 (H n (basisVec i, 0) x).2)
    covarianceBottom := fun n => 2 * ∑ i : Fin 2, (-E (S (0, basisVec i)) (C n (F false n i)) +
      ∑ j : Fin 2, energy Q (fun x => mainFlatMinusCoordinate Q b L n (i, j) x)) }

/-- Generic top-load trial expansion: only the source membership and its parent
shear-gauge variation are used. -/
theorem old_signed_generic_top_trial_expansion (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l})
    (H : whiteBasisIndex → BlockVec 2 → Vec 2 → BlockVec 2)
    (hH : ∀ n P, MemBlockL2 (openCubeSet Q) (H n P))
    (hgauge : ∀ n P, ScalarVariation (openCubeSet Q) (H n P -
      oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
        ((oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P : Vec 2 → BlockVec 2) -
          (fun _ => P))))
    (n : whiteBasisIndex) (i : Fin 2) :
    let E := oldSignedEnergyPairing Q nu sigma k
    let C := oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
    let S := oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (basisVec i, 0)
    let A := oldSignedPatchedPlus Q depth nu sigma hnu hsigma k b L n i
    let R := oldSignedLocalResidual Q depth nu sigma hnu hsigma k
      (H n (basisVec i, 0)) (hH n (basisVec i, 0))
    oldSignedPhysicalHessian Q nu sigma hnu hsigma k (basisVec i, 0) b L n ≤
      E A A + E R R + 2 * E A R + 2 * E S (C A) + 2 * E S (C R) := by
  intro E C S A R
  have hA : MemBlockL2 (openCubeSet Q) A :=
    old_signed_local_residual_memLp Q depth nu sigma hnu hsigma k _
      (old_signed_flat_plus_block_memL2 Q b L n i)
  have hR : MemBlockL2 (openCubeSet Q) R :=
    old_signed_local_residual_memLp Q depth nu sigma hnu hsigma k _ (hH n (basisVec i, 0))
  have hS : MemBlockL2 (openCubeSet Q) S := Lp.memLp S
  have hvar : ScalarVariation (openCubeSet Q) (A + R - C S) :=
    old_signed_local_top_trial_variation Q depth nu sigma hnu hsigma k
      (oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n)))
      (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (basisVec i, 0))
      (fun _ => (basisVec i, 0))
      (oldSignedFlatPlusBlock Q b L n i) (H n (basisVec i, 0))
      (old_signed_flat_plus_block_memL2 Q b L n i) (hH n (basisVec i, 0))
      (old_signed_flat_plus_pointwise_shear_variation Q b L n i)
      (hgauge n (basisVec i, 0))
  have hh : oldSignedPhysicalHessian Q nu sigma hnu hsigma k (basisVec i, 0) b L n ≤
      oldSignedPhysicalTrialValue Q nu sigma hnu hsigma k (basisVec i, 0) b L n (hA.add hR) :=
    old_signed_physical_trial_bound Q nu sigma hnu hsigma k b L n (basisVec i, 0)
      (hA.add hR) hvar
  rw [old_signed_trial_value_fields] at hh
  have he := old_signed_top_field_trial_expansion Q nu sigma hnu hsigma k b L n hS hA hR
  exact hh.trans_eq he

/-- Generic bottom-load trial expansion (negative mixed cross and feedback kept). -/
theorem old_signed_generic_bottom_trial_expansion (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l})
    (H : whiteBasisIndex → BlockVec 2 → Vec 2 → BlockVec 2)
    (hH : ∀ n P, MemBlockL2 (openCubeSet Q) (H n P))
    (hgauge : ∀ n P, ScalarVariation (openCubeSet Q) (H n P -
      oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
        ((oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P : Vec 2 → BlockVec 2) -
          (fun _ => P))))
    (n : whiteBasisIndex) (i : Fin 2) :
    let E := oldSignedEnergyPairing Q nu sigma k
    let C := oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
    let S := oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (0, basisVec i)
    let R := oldSignedLocalResidual Q depth nu sigma hnu hsigma k
      (H n (0, basisVec i)) (hH n (0, basisVec i))
    let Z := oldSignedPatchedMinus Q depth nu sigma hnu hsigma k b L n i
    oldSignedPhysicalHessian Q nu sigma hnu hsigma k (0, basisVec i) b L n ≤
      E R R + E Z Z - 2 * E R Z + 2 * E S (C R) - 2 * E S (C Z) := by
  intro E C S R Z
  have hR : MemBlockL2 (openCubeSet Q) R :=
    old_signed_local_residual_memLp Q depth nu sigma hnu hsigma k _ (hH n (0, basisVec i))
  have hZ : MemBlockL2 (openCubeSet Q) Z :=
    old_signed_local_residual_memLp Q depth nu sigma hnu hsigma k _
      (old_signed_flat_minus_block_memL2 Q b L n i)
  have hS : MemBlockL2 (openCubeSet Q) S := Lp.memLp S
  have hE : oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
      (fun _ => (0, basisVec i)) = 0 := by
    funext x
    simp [oldSignedPointwiseShear, matVecMul_zero]
  have hvar : ScalarVariation (openCubeSet Q) (R - Z - C S) :=
    old_signed_local_bottom_trial_variation Q depth nu sigma hnu hsigma k
      (oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n)))
      (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (0, basisVec i))
      (fun _ => (0, basisVec i))
      (H n (0, basisVec i)) (oldSignedFlatMinusBlock Q b L n i)
      (hH n (0, basisVec i)) (old_signed_flat_minus_block_memL2 Q b L n i) hE
      (hgauge n (0, basisVec i)) (old_signed_flat_minus_block_variation Q b L n i)
  have hh : oldSignedPhysicalHessian Q nu sigma hnu hsigma k (0, basisVec i) b L n ≤
      oldSignedPhysicalTrialValue Q nu sigma hnu hsigma k (0, basisVec i) b L n (hR.sub hZ) :=
    old_signed_physical_trial_bound Q nu sigma hnu hsigma k b L n (0, basisVec i)
      (hR.sub hZ) hvar
  rw [old_signed_trial_value_fields] at hh
  have he := old_signed_bottom_field_trial_expansion Q nu sigma hnu hsigma k b L n hS hR hZ
  exact hh.trans_eq he

/-- Generic assembly: per fresh mode the four canonical Hessians are bounded by
the signed total of the nine families of the generic trial. -/
theorem old_signed_generic_hessian_le_trial_total (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l})
    (H : whiteBasisIndex → BlockVec 2 → Vec 2 → BlockVec 2)
    (hH : ∀ n P, MemBlockL2 (openCubeSet Q) (H n P))
    (hgauge : ∀ n P, ScalarVariation (openCubeSet Q) (H n P -
      oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
        ((oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P : Vec 2 → BlockVec 2) -
          (fun _ => P))))
    (n : whiteBasisIndex) :
    (∑ c : BlockCoord 2, oldSignedPhysicalHessian Q nu sigma hnu hsigma k (blockBasis c) b L n) ≤
      (oldSignedGenericTrialTerms Q depth nu sigma hnu hsigma k b L H hH).total n := by
  have ht := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    old_signed_generic_top_trial_expansion Q depth nu sigma hnu hsigma k b L H hH hgauge n i)
  have hb := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    old_signed_generic_bottom_trial_expansion Q depth nu sigma hnu hsigma k b L H hH hgauge n i)
  have hh := add_le_add ht hb
  have hsym (i : Fin 2) := old_signed_energy_pairing_symm Q nu sigma k
    (oldSignedLocalResidual Q depth nu sigma hnu hsigma k (H n (0, basisVec i))
      (hH n (0, basisVec i)))
    (oldSignedPatchedMinus Q depth nu sigma hnu hsigma k b L n i)
  simp_rw [hsym] at hh
  rw [Fintype.sum_sum_type]
  apply hh.trans_eq
  have hl1 (i : Fin 2) : oldSignedLocalResidual Q depth nu sigma hnu hsigma k
      (H n (oldSignedFlatLoad true i)) (hH n (oldSignedFlatLoad true i)) =
      oldSignedLocalResidual Q depth nu sigma hnu hsigma k
        (H n (basisVec i, 0)) (hH n (basisVec i, 0)) := rfl
  have hl0 (i : Fin 2) : oldSignedLocalResidual Q depth nu sigma hnu hsigma k
      (H n (oldSignedFlatLoad false i)) (hH n (oldSignedFlatLoad false i)) =
      oldSignedLocalResidual Q depth nu sigma hnu hsigma k
        (H n (0, basisVec i)) (hH n (0, basisVec i)) := rfl
  have hv1 (i : Fin 2) (x : Vec 2) :
      H n (oldSignedFlatLoad true i) x = H n (basisVec i, 0) x := rfl
  have hv0 (i : Fin 2) (x : Vec 2) :
      H n (oldSignedFlatLoad false i) x = H n (0, basisVec i) x := rfl
  unfold OldSignedTrialTerms.total oldSignedGenericTrialTerms
  simp only [oldSignedFlatInput, hl1, hl0, hv1, hv0, Bool.false_eq_true, ite_false, ite_true,
    old_signed_patched_flat_true, old_signed_patched_flat_false, Fintype.sum_sum_type]
  have hminus (i : Fin 2) : volumeAverage (openCubeSet Q) (fun x =>
      vecDot (oldSignedFlatMinusBlock Q b L n i x).2 (H n (0, basisVec i) x).2) = 0 := by
    simp [oldSignedFlatMinusBlock, vecDot, volumeAverage]
  simp only [blockBasis, basisVec] at hminus ⊢
  simp only [hminus, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    ← Finset.mul_sum, oldSignedFlatDirichletModeEnergy]
  ring

/-- The nine signed families of the HOT-patched trial (source `f'`, depth-`depth`
tiling both for the local projection and the source interpolant). -/
def hotPatchTrialTerms (Q : TriadicCube 2) (depth : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l}) :
    OldSignedTrialTerms :=
  oldSignedGenericTrialTerms Q depth nu sigma hnu hsigma k b L
    (fun n P => hotPatchSource Q depth depth nu sigma hnu hsigma k b L n P)
    (fun n P => hot_patch_source_memL2 Q depth depth nu sigma hnu hsigma k b L n P)

/-- The hot-patched trial is admissible: per fresh mode the four canonical
Hessians are bounded by the signed total of its nine families. -/
theorem hot_patch_canonical_hessian_le_trial_total (Q : TriadicCube 2) (depth : ℕ)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l})
    (n : whiteBasisIndex) :
    (∑ c : BlockCoord 2, oldSignedPhysicalHessian Q nu sigma hnu hsigma k (blockBasis c) b L n) ≤
      (hotPatchTrialTerms Q depth nu sigma hnu hsigma k b L).total n :=
  old_signed_generic_hessian_le_trial_total Q depth nu sigma hnu hsigma k b L _ _
    (fun n P => hot_patch_source_gauge_variation Q depth depth nu sigma hnu hsigma k b L n P) n

end

end ASDExplicitGamma.Native
