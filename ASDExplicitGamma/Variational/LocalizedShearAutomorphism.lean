module

public import ASDExplicitGamma.Variational.LocalizedAdmissible

/-! The actual admissible-space automorphism, with inverse obtained by negating epsilon. -/

@[expose] public section
namespace ASDExplicitGamma.Variational
open Homogenization MeasureTheory ASDExplicitGamma.Response
open scoped ENNReal
noncomputable section

 theorem LocalizedAdmissibleState.ext {U : Set (Vec 2)} {P : BlockVec 2}
    {X Y : LocalizedAdmissibleState U P} (hr : X.correction=Y.correction) (hf : X.flux=Y.flux) : X=Y := by
  cases X
  cases Y
  cases hr
  cases hf
  rfl

variable {U : Set (Vec 2)} [IsFiniteMeasure (volumeMeasureOn U)]

 def localizedAdmissibleShear (hU : IsOpenBoundedConvexDomain U) (P : BlockVec 2)
    (I : H1Function U →ₗ[ℝ] H1Function U) (η : H1Function U)
    (hη : MemLp η.toFun ⊤ (volume.restrict U))
    (hDη : ∀ i, MemLp (fun x => η.grad x i) ⊤ (volume.restrict U))
    (hres : ∀ r : H10Function U, MemH10 U (lemmaVAffinePotential hU P.1 r-I (lemmaVAffinePotential hU P.1 r)).toFun)
    (ε σ : ℝ) (Z : LocalizedAdmissibleState U P) : LocalizedAdmissibleState U P := by
  let v := lemmaVAffinePotential hU P.1 Z.correction
  let D := localizedColumnProductDivergence η (v-I v)
  have hD : MemVectorL2 U D := localizedColumnProductDivergence_memL2 η (v-I v) hη hDη
  have hDs : IsSolenoidalZeroNormalTraceOn U D :=
    localizedColumnProductDivergence_solenoidal hU η (v-I v) (hres Z.correction) hη hDη
  have hneg : MemVectorL2 U ((-(ε/σ)) • D) := hD.const_smul _
  have hsol := isSolenoidalZeroNormalTraceOn_add Z.flux_solenoidal
    (isSolenoidalZeroNormalTraceOn_smul hDs (-(ε/σ)))
    (fun w => integrableOn_vecDot_of_memVectorL2 Z.flux_memL2 w.grad_memVectorL2)
    (fun w => integrableOn_vecDot_of_memVectorL2 hneg w.grad_memVectorL2)
  have he : (fun x => Z.flux x-(ε/σ) • D x-P.2) = (fun x => Z.flux x-P.2)+(-(ε/σ)) • D := by
    funext x i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  exact {
    correction := Z.correction
    flux := fun x => Z.flux x-(ε/σ) • D x
    flux_memL2 := by rw [he]; exact Z.flux_memL2.add hneg
    flux_solenoidal := by rw [he]; exact hsol }

 theorem localizedAdmissibleShear_inverse (hU : IsOpenBoundedConvexDomain U) (P : BlockVec 2)
    (I : H1Function U →ₗ[ℝ] H1Function U) (η : H1Function U)
    (hη : MemLp η.toFun ⊤ (volume.restrict U))
    (hDη : ∀ i, MemLp (fun x => η.grad x i) ⊤ (volume.restrict U))
    (hres : ∀ r : H10Function U, MemH10 U (lemmaVAffinePotential hU P.1 r-I (lemmaVAffinePotential hU P.1 r)).toFun)
    (ε σ : ℝ) (Z : LocalizedAdmissibleState U P) :
    localizedAdmissibleShear hU P I η hη hDη hres (-ε) σ
      (localizedAdmissibleShear hU P I η hη hDη hres ε σ Z) = Z := by
  apply LocalizedAdmissibleState.ext
  · rfl
  · funext x i
    simp only [localizedAdmissibleShear, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring

 def localizedAdmissibleShearEquiv (hU : IsOpenBoundedConvexDomain U) (P : BlockVec 2)
    (I : H1Function U →ₗ[ℝ] H1Function U) (η : H1Function U)
    (hη : MemLp η.toFun ⊤ (volume.restrict U))
    (hDη : ∀ i, MemLp (fun x => η.grad x i) ⊤ (volume.restrict U))
    (hres : ∀ r : H10Function U, MemH10 U (lemmaVAffinePotential hU P.1 r-I (lemmaVAffinePotential hU P.1 r)).toFun)
    (ε σ : ℝ) : LocalizedAdmissibleState U P ≃ LocalizedAdmissibleState U P where
  toFun := localizedAdmissibleShear hU P I η hη hDη hres ε σ
  invFun := localizedAdmissibleShear hU P I η hη hDη hres (-ε) σ
  left_inv := localizedAdmissibleShear_inverse hU P I η hη hDη hres ε σ
  right_inv Z := by
    simpa only [neg_neg] using localizedAdmissibleShear_inverse hU P I η hη hDη hres (-ε) σ Z

 theorem localizedAdmissibleShear_composition (hU : IsOpenBoundedConvexDomain U) (P : BlockVec 2)
    (I : H1Function U →ₗ[ℝ] H1Function U) (η : H1Function U)
    (hη : MemLp η.toFun ⊤ (volume.restrict U))
    (hDη : ∀ i, MemLp (fun x => η.grad x i) ⊤ (volume.restrict U))
    (hres : ∀ r : H10Function U, MemH10 U (lemmaVAffinePotential hU P.1 r-I (lemmaVAffinePotential hU P.1 r)).toFun)
    (ε σ : ℝ) (Z : LocalizedAdmissibleState U P) (x : Vec 2) :
    responseShear σ (ε*η.toFun x)
      ((localizedAdmissibleShear hU P I η hη hDη hres ε σ Z).field.eval x) =
      ((lemmaVAffinePotential hU P.1 Z.correction).grad x,
        Z.flux x-(ε/σ) • lemmaVPlanarRowField I η (lemmaVAffinePotential hU P.1 Z.correction) x) := by
  have hg : (lemmaVAffinePotential hU P.1 Z.correction).grad x = Z.field.potential x := by
    simp only [lemmaVAffinePotential, H1Function.add_grad, H1Function.affineOnIsSobolevRegularDomain_grad,
      LocalizedAdmissibleState.field]
  apply Prod.ext
  · change Z.field.potential x + 0 = _
    simpa only [add_zero] using hg.symm
  · have hid := congrFun (localizedColumnProductDivergence_row_identity I η
      (lemmaVAffinePotential hU P.1 Z.correction)) x
    rw [← hid]
    funext i
    simp only [responseShear, responseShearCorrection, localizedAdmissibleShear,
      LocalizedAdmissibleState.field, BlockState.eval, Prod.snd_add, Pi.add_apply,
      Pi.neg_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hg]
    ring

end
end ASDExplicitGamma.Variational
