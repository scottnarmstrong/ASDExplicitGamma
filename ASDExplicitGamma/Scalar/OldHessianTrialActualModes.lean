module

public import ASDExplicitGamma.Scalar.OldHessianTrialModeTrial
public import ASDExplicitGamma.Scalar.OldHessianTrialInverseGenerator
public import ASDExplicitGamma.Scalar.OldHessianTrialSourceCrossMode
public import ASDExplicitGamma.Scalar.OldHessianTrialFullAffineIdentity
public import ASDExplicitGamma.Scalar.OldHessianTrialFlatTangent
public import ASDExplicitGamma.Scalar.OldHessianTrialNinthBill
public import ASDExplicitGamma.Scalar.OldHessianTrialSixthTenthBills
public import ASDExplicitGamma.Scalar.OldHessianTrialSeventhBill
public import ASDExplicitGamma.Scalar.OldHessianTrialSecondBill
public import ASDExplicitGamma.Scalar.OldHessianTrialFirstBill

/-! The actual physical Hessian modes of the OLD cutoff and their exact
decomposition into the ten frozen bills, mode by mode. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main Algsuperdiff.Section3
open Numerics.Mirror Numerics.Scalar
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

/-- Both bottom-load physical Hessians of one white mode, in the original OLD medium. -/
def oldHessianActualHessianMode (M : ABKModel 2) (m : ℤ) (b : ℝ)
    (n : whiteBasisIndex) (ω : Cutoff.CutoffSample 2) : ℝ :=
  ∑ i : Fin 2,oldSignedPhysicalHessian (originCube 2 (m+129)) M.nu (Annealed.sigmaBar M m) M.nu_pos
    (Annealed.sigmaBar_characterization M m).1 (oldHessianOldOpenCoefficient (m+129) m ω)
    (0,basisVec i) b (q3ModelLength (m+1)) n

/-- The mixed residual energy of one white mode. -/
def oldHessianResidualModeEnergy (M : ABKModel 2) (m : ℤ) (b : ℝ)
    (n : whiteBasisIndex) (ω : Cutoff.CutoffSample 2) : ℝ :=
  ∑ i : Fin 2,
    let R := oldHessianMixedBottomResidual (originCube 2 (m+129)) 133 134 M.nu (Annealed.sigmaBar M m)
      M.nu_pos (Annealed.sigmaBar_characterization M m).1 (oldHessianOldOpenCoefficient (m+129) m ω)
      b (q3ModelLength (m+1)) n i
    oldSignedEnergyPairing (originCube 2 (m+129)) M.nu (Annealed.sigmaBar M m)
      (oldHessianOldOpenCoefficient (m+129) m ω) R R

/-- Exact mode-by-mode trial decomposition into the named signed bills. -/
theorem old_hessian_actual_mode_decomposition (M : ABKModel 2) (m : ℤ) (b : ℝ)
    (n : whiteBasisIndex) (ω : Cutoff.CutoffSample 2) :
    oldHessianActualHessianMode M m b n ω ≤
      oldHessianResidualModeEnergy M m b n ω+
      (431/500:ℝ)^2*oldHessianMinusFlatEnergyTerm M m b (q3ModelLength (m+1)) n ω+
      (oldHessianFullAffineTerm M m b n ω-
        2*(431/500:ℝ)*(∑ i : Fin 2,oldHessianSourceOscillationTerm M m b (n,i) ω))+
      oldHessianMixedFeedbackTerm M m b n ω+
      (oldHessianFlatTangentTerm M m b n ω-
        2*(431/500:ℝ)*oldSignedFlatDirichletModeEnergy (originCube 2 (m+129)) b (q3ModelLength (m+1)) n-
        oldHessianMinusFeedbackTerm M m b n ω) := by
  let Q := originCube 2 (m+129)
  let k := oldHessianOldOpenCoefficient (m+129) m ω
  let σ := Annealed.sigmaBar M m
  let L := q3ModelLength (m+1)
  have hσ := (Annealed.sigmaBar_characterization M m).1
  let E := oldSignedEnergyPairing Q M.nu σ k
  let C := oldSignedPointwiseShear (q3Convolution b L h3Zero (whiteBasis n))
  let S := fun i : Fin 2 => oldSignedFrameCanonicalField Q M.nu σ M.nu_pos hσ k (0,basisVec i)
  let R := fun i : Fin 2 => oldHessianMixedBottomResidual Q 133 134 M.nu σ M.nu_pos hσ k b L n i
  let Z := fun i : Fin 2 => oldSignedPatchedMinus Q 134 M.nu σ M.nu_pos hσ k b L n i
  let F := fun i : Fin 2 => oldSignedFlatMinusBlock Q b L n i
  have hi (i : Fin 2) := old_hessian_mode_trial Q 133 M.nu σ M.nu_pos hσ k b L n i (431/500:ℝ)
  have hsum : oldHessianActualHessianMode M m b n ω ≤ ∑ i : Fin 2,
      (E (R i) (R i)+(431/500:ℝ)^2*E (Z i) (Z i)-2*(431/500:ℝ)*E (R i) (Z i)+2*E (S i) (C (R i))-2*(431/500:ℝ)*E (S i) (C (Z i))) :=
    Finset.sum_le_sum (fun i _ => hi i)
  refine hsum.trans_eq ?_
  have hcross := old_hessian_source_cross_mode Q 133 M.nu σ M.nu_pos hσ k b L n (431/500:ℝ)
  have hso : oldHessianSourceOscillationSpatialMode Q 133 M.nu σ M.nu_pos hσ k b L n =
      ∑ i : Fin 2,oldHessianSourceOscillationTerm M m b (n,i) ω := by
    unfold oldHessianSourceOscillationSpatialMode oldHessianSourceOscillationTerm
    rw [old_signed_cell_average_sum]
  have hfb : oldHessianMixedFeedbackTerm M m b n ω = 2*∑ i : Fin 2,E (S i) (C (R i)) := rfl
  have hflat : oldHessianFlatTangentTerm M m b n ω-2*(431/500:ℝ)*oldSignedFlatDirichletModeEnergy Q b L n-
      oldHessianMinusFeedbackTerm M m b n ω = -2*(431/500:ℝ)*∑ i : Fin 2,E (S i) (C (Z i)) := by
    unfold oldHessianFlatTangentTerm oldHessianMinusFeedbackTerm oldSignedFlatDirichletModeEnergy
    have hb (i : Fin 2) : blockBasis (Sum.inr i)=((0:Vec 2),basisVec i) := rfl
    simp only [hb,Finset.sum_add_distrib,Finset.sum_neg_distrib,←Finset.mul_sum]
    linarith
  have hrr : oldHessianResidualModeEnergy M m b n ω = ∑ i : Fin 2,E (R i) (R i) := rfl
  have hzz : oldHessianMinusFlatEnergyTerm M m b L n ω = ∑ i : Fin 2,E (Z i) (Z i) := rfl
  have hfa : oldHessianFullAffineTerm M m b n ω = (2*(431/500:ℝ))*
      oldHessianFullAffineSpatialMode Q 133 M.nu σ M.nu_pos hσ k b L n := rfl
  rw [hrr,hzz,hfb,hfa,←hso]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum] at hcross hflat ⊢
  linarith only [hcross,hflat]

end
end ASDExplicitGamma.Scalar
