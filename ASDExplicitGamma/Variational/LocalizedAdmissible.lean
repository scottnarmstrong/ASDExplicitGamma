module

public import ASDExplicitGamma.Variational.LemmaVMinimizer
public import ASDExplicitGamma.Variational.LocalizedShearWeak
public import Homogenization.CoarseGraining.MuAdmissibility

/-! Genuine potential/flux representatives of the canonical Mu admissible affine space. -/

@[expose] public section
namespace ASDExplicitGamma.Variational
open Homogenization MeasureTheory
noncomputable section

/-- An actual zero-boundary potential correction and actual affine solenoidal flux. -/
structure LocalizedAdmissibleState (U : Set (Vec 2)) (P : BlockVec 2) where
  correction : H10Function U
  flux : Vec 2 → Vec 2
  flux_memL2 : MemVectorL2 U (fun x => flux x-P.2)
  flux_solenoidal : IsSolenoidalZeroNormalTraceOn U (fun x => flux x-P.2)

 def LocalizedAdmissibleState.field {U : Set (Vec 2)} {P : BlockVec 2}
    (Z : LocalizedAdmissibleState U P) : BlockState 2 where
  potential x := P.1+Z.correction.toH1Function.grad x
  flux := Z.flux

 theorem LocalizedAdmissibleState.field_admissible {U : Set (Vec 2)} {P : BlockVec 2}
    (Z : LocalizedAdmissibleState U P) : IsBlockMuAdmissible U P Z.field := by
  have he : (fun x => Z.field.potential x-P.1) = Z.correction.toH1Function.grad := by
    funext x
    simp only [LocalizedAdmissibleState.field, add_sub_cancel_left]
  change MemVectorL2 U _ ∧ IsPotentialZeroTraceOn U _ ∧ _ ∧ _
  rw [he]
  exact ⟨Z.correction.toH1Function.grad_memVectorL2, ⟨Z.correction,rfl⟩, Z.flux_memL2, Z.flux_solenoidal⟩

/-- Every canonical Mu competitor is exactly represented, including its flux and potential fields.
Thus no smaller auxiliary minimization space has been substituted. -/
theorem localizedAdmissibleState_surjective {U : Set (Vec 2)} {P : BlockVec 2}
    (X : BlockState 2) (hX : IsBlockMuAdmissible U P X) :
    ∃ Z : LocalizedAdmissibleState U P, Z.field = X := by
  obtain ⟨r,hr⟩ := hX.isPotentialZeroTrace
  let Z : LocalizedAdmissibleState U P := ⟨r,X.flux,hX.fluxCorrection_memL2,hX.isSolenoidalZeroNormalTrace⟩
  refine ⟨Z,BlockState.ext ?_ rfl⟩
  funext x i
  have hri := congrFun (congrFun hr x) i
  change P.1 i+r.toH1Function.grad x i = X.potential x i
  change r.toH1Function.grad x i = X.potential x i-P.1 i at hri
  linarith only [hri]

/-- Source admissible energy values, for any energy functional at all, are unchanged by this representation. -/
theorem localizedAdmissibleState_energy_range {U : Set (Vec 2)} {P : BlockVec 2}
    (E : BlockState 2 → ℝ) :
    {e : ℝ | ∃ X : BlockState 2, IsBlockMuAdmissible U P X ∧ e=E X} =
      Set.range (fun Z : LocalizedAdmissibleState U P => E Z.field) := by
  ext e
  constructor
  · rintro ⟨X,hX,rfl⟩
    obtain ⟨Z,hZ⟩ := localizedAdmissibleState_surjective X hX
    exact ⟨Z,congrArg E hZ⟩
  · rintro ⟨Z,rfl⟩
    exact ⟨Z.field,Z.field_admissible,rfl⟩

end
end ASDExplicitGamma.Variational
