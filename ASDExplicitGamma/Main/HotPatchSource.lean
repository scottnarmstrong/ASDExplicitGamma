module

public import ASDExplicitGamma.Main.HotPatchGap
public import ASDExplicitGamma.Scalar.OldHessianTrialCoarsePotential
public import ASDExplicitGamma.Native.OldSignedOldErrorSource
public import ASDExplicitGamma.Native.OldSignedActualTrialVariation

/-! Hot-patch trial, package B (source): the glued local first corrector `φ`,
the hot-patched source `f' = F(w) + φ div H` and its parent shear-gauge
variation. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open Homogenization MeasureTheory ASDExplicitGamma.Scalar ASDExplicitGamma.Main
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Response ASDExplicitGamma.Triadic
open ASDExplicitGamma.Variational

noncomputable section

/-- The glued local first corrector of the constant load `P` on the depth-`depth`
source tiling: the zero extensions of the actual cell first correctors. -/
def hotGluedCorrector (Q : TriadicCube 2) (depth : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    H10Function (openCubeSet Q) :=
  oldHessianH10Sum Finset.univ
    (fun R : {R : TriadicCube 2 // R ∈ descendantsAtDepth Q depth} =>
      (oldSignedCellFirstCorrector Q R.1
        (openCubeSet_subset_of_mem_descendantsAtDepth R.2) nu sigma hnu hsigma k
        (fun _ => P) (memLp_const P)).extendByZeroToOpenSuperset
        (measurableSet_openCubeSet R.1) (isOpen_openCubeSet Q)
        (openCubeSet_subset_of_mem_descendantsAtDepth R.2))

/-- Almost every point of the parent lies in an open depth-`depth` cell. -/
theorem hot_ae_exists_cell (Q : TriadicCube 2) (depth : ℕ) :
    ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q),
      ∃ R ∈ descendantsAtDepth Q depth, x ∈ openCubeSet R := by
  classical
  have hnotBoundary : ∀ᵐ x ∂volume, ∀ R : {R : TriadicCube 2 // R ∈ descendantsAtDepth Q depth},
      x ∉ cubeBoundary R.1 := by
    rw [ae_all_iff]
    intro R
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using volume_cubeBoundary_eq_zero R.1
  apply (ae_restrict_iff' (measurableSet_openCubeSet Q)).2
  filter_upwards [hnotBoundary] with x hnb hxQ
  obtain ⟨R, hR, hxCube⟩ := exists_mem_descendantsAtDepth_of_mem_cubeSet depth
    (openCubeSet_subset_cubeSet Q hxQ)
  refine ⟨R, hR, ?_⟩
  by_contra hxR
  exact hnb ⟨R, hR⟩ ⟨hxCube, hxR⟩

/-- On each open cell the glued corrector is the actual cell corrector. -/
theorem hot_glued_corrector_cell (Q : TriadicCube 2) (depth : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2)
    (R : TriadicCube 2) (hR : R ∈ descendantsAtDepth Q depth) (x : Vec 2)
    (hx : x ∈ openCubeSet R) :
    (hotGluedCorrector Q depth nu sigma hnu hsigma k P).toH1Function x =
      (oldSignedCellFirstCorrector Q R
        (openCubeSet_subset_of_mem_descendantsAtDepth hR) nu sigma hnu hsigma k
        (fun _ => P) (memLp_const P)).toH1Function x := by
  classical
  unfold hotGluedCorrector
  rw [old_hessian_h10_sum_fun]
  dsimp only
  rw [Fintype.sum_eq_single ⟨R, hR⟩]
  · simp [H10Function.zeroExtension, hx]
  · intro S hne
    have hSR : S.1 ≠ R := fun heq => hne (Subtype.ext heq)
    have hd := pairwiseDisjoint_openCubeSet_descendantsAtDepth Q depth S.2 hR hSR
    have hxS : x ∉ openCubeSet S.1 := fun hxs => (Set.disjoint_left.mp hd) hxs hx
    simp [H10Function.zeroExtension, hxS]

/-- On each open cell the glued corrector has the gradient of the cell corrector. -/
theorem hot_glued_corrector_grad_cell (Q : TriadicCube 2) (depth : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2)
    (R : TriadicCube 2) (hR : R ∈ descendantsAtDepth Q depth) (x : Vec 2)
    (hx : x ∈ openCubeSet R) :
    (hotGluedCorrector Q depth nu sigma hnu hsigma k P).toH1Function.grad x =
      (oldSignedCellFirstCorrector Q R
        (openCubeSet_subset_of_mem_descendantsAtDepth hR) nu sigma hnu hsigma k
        (fun _ => P) (memLp_const P)).toH1Function.grad x := by
  classical
  unfold hotGluedCorrector
  rw [old_hessian_h10_sum_grad]
  dsimp only
  rw [Fintype.sum_eq_single ⟨R, hR⟩]
  · rw [H10Function.extendByZeroToOpenSuperset_grad]
    simp [H10Function.zeroExtensionGrad, hx]
  · intro S hne
    have hSR : S.1 ≠ R := fun heq => hne (Subtype.ext heq)
    have hd := pairwiseDisjoint_openCubeSet_descendantsAtDepth Q depth S.2 hR hSR
    have hxS : x ∉ openCubeSet S.1 := fun hxs => (Set.disjoint_left.mp hd) hxs hx
    rw [H10Function.extendByZeroToOpenSuperset_grad]
    simp [H10Function.zeroExtensionGrad, hxS]

/-- Almost everywhere, the glued corrector differentiates to the first block of
the glued local residual minus the load. -/
theorem hot_glued_corrector_grad_ae (Q : TriadicCube 2) (depth : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q),
      (hotGluedCorrector Q depth nu sigma hnu hsigma k P).toH1Function.grad x =
        (oldSignedLocalResidual Q depth nu sigma hnu hsigma k (fun _ => P)
          (memLp_const P) x).1 - P.1 := by
  classical
  filter_upwards [hot_ae_exists_cell Q depth] with x ⟨R, hR, hxR⟩
  rw [hot_glued_corrector_grad_cell Q depth nu sigma hnu hsigma k P R hR x hxR,
    old_signed_cell_first_corrector_grad]
  have hres : oldSignedLocalResidual Q depth nu sigma hnu hsigma k (fun _ => P)
      (memLp_const P) x =
      oldSignedCellResidual Q R (openCubeSet_subset_of_mem_descendantsAtDepth hR)
        nu sigma hnu hsigma k (fun _ => P) (memLp_const P) x := by
    change (∑ S : {R : TriadicCube 2 // R ∈ descendantsAtDepth Q depth},
      (openCubeSet S.1).indicator
        (oldSignedCellResidual Q S.1
          (openCubeSet_subset_of_mem_descendantsAtDepth S.2)
          nu sigma hnu hsigma k (fun _ => P) (memLp_const P)) x) = _
    rw [Fintype.sum_eq_single (⟨R, hR⟩ : {R : TriadicCube 2 // R ∈ descendantsAtDepth Q depth})]
    · rw [Set.indicator_of_mem (by simpa using hxR)]
    · intro S hSi
      have hne : S.1 ≠ R := fun heq => hSi (Subtype.ext heq)
      have hdisj := pairwiseDisjoint_openCubeSet_descendantsAtDepth Q depth S.2 hR hne
      have hxS : x ∉ openCubeSet S.1 := fun hxS => (Set.disjoint_left.mp hdisj) hxS hxR
      simp [hxS]
  rw [hres]

/-- The zero-trace first potential `w` of the patch drop (chosen). -/
def hotPatchPotential (Q : TriadicCube 2) (depth : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    H10Function (openCubeSet Q) :=
  (hot_patch_drop_potential Q depth nu sigma hnu hsigma k P).choose

theorem hotPatchPotential_grad (Q : TriadicCube 2) (depth : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    (hotPatchPotential Q depth nu sigma hnu hsigma k P).toH1Function.grad =
      fun x => (hotPatchDrop Q depth nu sigma hnu hsigma k P x).1 :=
  (hot_patch_drop_potential Q depth nu sigma hnu hsigma k P).choose_spec

/-- The hot-patched source `f' = F(w) + φ div H` (as the doubled field `(0,-f')`):
the localized row shear of the coarse potential `w` through the DIAG interpolant,
plus the uninterpolated product `φ div H` of the glued local corrector. -/
def hotPatchSource (Q : TriadicCube 2) (depth mesh : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l})
    (n : whiteBasisIndex) (P : BlockVec 2) : Vec 2 → BlockVec 2 := fun x =>
  oldSignedLocalizedPotentialShear (diagInterpolant Q mesh)
      (mainQ3DirectionW2 Q b L (whiteBasis n)).value
      (hotPatchPotential Q depth nu sigma hnu hsigma k P).toH1Function x +
    oldSignedLocalizedPotentialShear
      (0 : H1Function (openCubeSet Q) →ₗ[ℝ] H1Function (openCubeSet Q))
      (mainQ3DirectionW2 Q b L (whiteBasis n)).value
      (hotGluedCorrector Q depth nu sigma hnu hsigma k P).toH1Function x

theorem hot_patch_source_memL2 (Q : TriadicCube 2) (depth mesh : ℕ) (nu sigma : ℝ)
    (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l})
    (n : whiteBasisIndex) (P : BlockVec 2) :
    MemBlockL2 (openCubeSet Q) (hotPatchSource Q depth mesh nu sigma hnu hsigma k b L n P) :=
  (old_signed_localized_potential_shear_memL2 Q (diagInterpolant Q mesh) _ _
    (mainQ3DirectionW2 Q b L (whiteBasis n)).value_memLp_top
    (mainQ3DirectionW2 Q b L (whiteBasis n)).gradient_memLp_top_volume).add
  (old_signed_localized_potential_shear_memL2 Q _ _ _
    (mainQ3DirectionW2 Q b L (whiteBasis n)).value_memLp_top
    (mainQ3DirectionW2 Q b L (whiteBasis n)).gradient_memLp_top_volume)

/-- The hot-patched source differs from the physical pointwise shear of the
canonical error by a genuine parent variation: the difference is
`H_j∇u − F(u)`-type for `w` and for `φ`, each solenoidal with zero normal trace. -/
theorem hot_patch_source_gauge_variation (Q : TriadicCube 2) (depth mesh : ℕ)
    (nu sigma : ℝ) (hnu : 0 < nu) (hsigma : 0 < sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (b : ℝ) (L : {l : ℝ // 0 < l})
    (n : whiteBasisIndex) (P : BlockVec 2) :
    ScalarVariation (openCubeSet Q)
      (hotPatchSource Q depth mesh nu sigma hnu hsigma k b L n P -
        oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
          ((oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P :
            Vec 2 → BlockVec 2) - (fun _ => P))) := by
  classical
  let eta := (mainQ3DirectionW2 Q b L (whiteBasis n)).value
  let w := hotPatchPotential Q depth nu sigma hnu hsigma k P
  let φ := hotGluedCorrector Q depth nu sigma hnu hsigma k P
  have hw := hotPatchPotential_grad Q depth nu sigma hnu hsigma k P
  have h1 := old_signed_localized_physical_shear_variation Q (diagInterpolant Q mesh) eta
    w.toH1Function
    (by simpa only [H1Function.sub_toFun] using
      memH10_sub w.memH10 (diagInterpolant_h10_memH10 Q mesh w))
    (mainQ3DirectionW2 Q b L (whiteBasis n)).value_memLp_top
    (mainQ3DirectionW2 Q b L (whiteBasis n)).gradient_memLp_top_volume
  have h2 := old_signed_localized_physical_shear_variation Q
    (0 : H1Function (openCubeSet Q) →ₗ[ℝ] H1Function (openCubeSet Q)) eta φ.toH1Function
    (by simpa using φ.memH10)
    (mainQ3DirectionW2 Q b L (whiteBasis n)).value_memLp_top
    (mainQ3DirectionW2 Q b L (whiteBasis n)).gradient_memLp_top_volume
  have hsum := scalar_variation_add h1 h2
  refine old_signed_scalar_variation_congr_ae ?_ hsum
  filter_upwards [hot_glued_corrector_grad_ae Q depth nu sigma hnu hsigma k P] with x hx
  have hwx : w.toH1Function.grad x =
      (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P x).1 -
        (oldSignedLocalResidual Q depth nu sigma hnu hsigma k (fun _ => P)
          (memLp_const P) x).1 := by
    rw [hw]; rfl
  have hsplit : (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P x).1 - P.1 =
      ((oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P x).1 -
        (oldSignedLocalResidual Q depth nu sigma hnu hsigma k (fun _ => P)
          (memLp_const P) x).1) +
      ((oldSignedLocalResidual Q depth nu sigma hnu hsigma k (fun _ => P)
          (memLp_const P) x).1 - P.1) := by abel
  simp only [hotPatchSource, oldSignedLocalizedPotentialShear,
    oldSignedPhysicalPotentialShear, oldSignedPointwiseShear, LinearMap.coe_mk,
    AddHom.coe_mk, Pi.add_apply, Pi.sub_apply]
  rw [hwx, hx]
  apply Prod.ext
  · simp
  · simp only [Prod.snd_add, Prod.snd_sub]
    have hS1 : ((oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P x) - P).1 =
        (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P x).1 - P.1 := rfl
    have hη : q3Convolution b L h3Zero (whiteBasis n) x = eta.toFun x := rfl
    rw [hS1, hη, hsplit, matVecMul_add, smul_add]
    simp only [eta, w, φ]
    abel

end

end ASDExplicitGamma.Native
