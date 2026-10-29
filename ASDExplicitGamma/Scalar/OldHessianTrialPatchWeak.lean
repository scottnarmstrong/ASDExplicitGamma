module

public import ASDExplicitGamma.Scalar.OldHessianTrialCoarsePotential
public import ASDExplicitGamma.Scalar.OldHessianTrialPatchDrop
public import ASDExplicitGamma.Native.ParentBoundaryCompatibleWeak

/-! Fine-history coercivity for the actual coarse bottom comparison.
The source split uses coarse potentials; its norm uses the original fine history. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- The original fine complete inverse-history maximum, in the same frame
and coefficient as the physical mixed trial. -/
def oldHessianFineInverseHistory (Q : TriadicCube 2) (fine : ℕ)
    (nu sigma : ℝ) (k : ResponseCoefficient (openCubeSet Q)) : ℝ :=
  Book.Ch02.finsetSupReal (descendantsAtDepth Q fine) (fun U =>
    lemmaVInverseHistory U (responseFramePlanarCoefficientField nu sigma k)
      ((3:ℝ)^(1/4:ℝ)))

/-- Each fine-cell history is below that literal finite maximum. -/
theorem old_hessian_fine_history_le (Q : TriadicCube 2) (fine : ℕ)
    (nu sigma : ℝ) (k : ResponseCoefficient (openCubeSet Q))
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q fine) :
    lemmaVInverseHistory U (responseFramePlanarCoefficientField nu sigma k)
      ((3:ℝ)^(1/4:ℝ)) ≤ oldHessianFineInverseHistory Q fine nu sigma k := by
  unfold oldHessianFineInverseHistory Book.Ch02.finsetSupReal
  exact le_csSup (((Set.toFinite _).image _).bddAbove) ⟨U,hU,rfl⟩

/-- Coarse patching changes the source potential but not the fine inverse
history in its complete weak norm. The right side is the actual patch drop. -/
theorem old_hessian_coarse_patch_fine_weak (Q : TriadicCube 2) (coarse fine : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (P : BlockVec 2) :
    let S : Vec 2 → BlockVec 2 := oldSignedFrameCanonicalField Q nu sigma hnu hsigma k P
    let L := oldSignedLocalResidual Q coarse nu sigma hnu hsigma k (fun _ => P) (memLp_const P)
    lemmaVTiledWeakEnergy Q fine (fun x => (S x-L x).1) ≤
      oldHessianFineInverseHistory Q fine nu sigma k*
        oldHessianPatchDrop Q coarse nu sigma hnu hsigma k P := by
  intro S L
  exact parent_boundary_compatible_tiled_weak Q fine nu sigma hnu hsigma k _
    (old_signed_compatible_sub (old_signed_canonical_compatible Q nu sigma hnu hsigma k P)
      (old_signed_patch_compatible Q coarse nu sigma hnu hsigma k P))
    (old_hessian_fine_history_le Q fine nu sigma k)

/-- The split first gradient is literally the actual bottom parent-minus-
coarse-patch first field, not an independently chosen admissible surrogate. -/
theorem old_hessian_coarse_split_gradient (Q : TriadicCube 2) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (e : Vec 2) :
    let a := responseFramePlanarCoefficientField nu sigma k
    let ha := responseFramePlanarCoefficientField_isElliptic
      (measurableSet_openCubeSet Q) nu sigma hnu hsigma k
    let v := oldSignedCanonicalFirstCorrector Q a ha (0,e)
    let phi := oldHessianCoarsePotential Q coarse nu sigma hnu hsigma k e
    (v.toH1Function-phi.toH1Function).grad =
      (fun x => (oldSignedFrameCanonicalField Q nu sigma hnu hsigma k (0,e) x-
        oldSignedLocalResidual Q coarse nu sigma hnu hsigma k (fun _ => (0,e))
          (memLp_const (0,e)) x).1) := by
  intro a ha v phi
  rw [H1Function.sub_grad,old_signed_canonical_first_corrector_grad,
    old_hessian_coarse_potential_grad]
  funext x
  exact congrArg (fun z : Vec 2 => z-
    (oldSignedLocalResidual Q coarse nu sigma hnu hsigma k (fun _ => (0,e))
      (memLp_const (0,e)) x).1) (sub_zero _)

/-- The two actual mixed source potentials obey the sharp fine-history
energy estimate, with the genuine coarse two-load patch drop retained. -/
theorem old_hessian_mixed_potential_weak (Q : TriadicCube 2) (coarse fine : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) :
    let a := responseFramePlanarCoefficientField nu sigma k
    let ha := responseFramePlanarCoefficientField_isElliptic
      (measurableSet_openCubeSet Q) nu sigma hnu hsigma k
    let v := fun i : Fin 2 => oldSignedCanonicalFirstCorrector Q a ha (0,basisVec i)
    let phi := fun i : Fin 2 => oldHessianCoarsePotential Q coarse nu sigma hnu hsigma k (basisVec i)
    (∑ i : Fin 2,lemmaVTiledWeakEnergy Q fine
      ((v i).toH1Function-(phi i).toH1Function).grad) ≤
      oldHessianFineInverseHistory Q fine nu sigma k*
        ∑ i : Fin 2,oldHessianPatchDrop Q coarse nu sigma hnu hsigma k (0,basisVec i) := by
  intro a ha v phi
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    old_hessian_coarse_patch_fine_weak Q coarse fine nu sigma hnu hsigma k (0,basisVec i))
  rw [←Finset.mul_sum] at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i _
  rw [old_hessian_coarse_split_gradient]

end
end ASDExplicitGamma.Scalar
