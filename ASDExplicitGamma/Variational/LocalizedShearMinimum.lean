module

public import ASDExplicitGamma.Variational.LocalizedShearAutomorphism

/-! Exact canonical minimum reparametrization by the localized shear. -/

@[expose] public section
namespace ASDExplicitGamma.Variational
open Homogenization MeasureTheory ASDExplicitGamma.Response
open scoped ENNReal
noncomputable section
variable {U : Set (Vec 2)} [IsFiniteMeasure (volumeMeasureOn U)]

def responseFrameEnergyValueSet (P : BlockVec 2) (ν σ : ℝ) (k : ResponseCoefficient U) : Set ℝ :=
  {e | ∃ X : BlockState 2, IsBlockMuAdmissible U P X ∧ e = volumeAverage U
    (fun x => responseFrameEnergyDensity ν σ (responseCoefficientExtension k x) (X.eval x))}

 theorem responseFrameEnergyDensity_eq_twice_blockEnergyDensity (ν σ : ℝ)
    (hν : 0 < ν) (hσ : 0 < σ) (k : ResponseCoefficient U)
    (X : BlockState 2) (x : Vec 2) :
    responseFrameEnergyDensity ν σ (responseCoefficientExtension k x) (X.eval x) =
      2 * blockEnergyDensity (responseFramePlanarCoefficientField ν σ k) X x := by
  rw [responseFrameEnergyDensity_eq_scaledCoefficientBlock ν σ (responseCoefficientExtension k x) hν hσ (X.eval x)]
  simp [blockEnergyDensity, blockCoeffField, responseFramePlanarCoefficientField]

 theorem sInf_image_mul_two {S : Set ℝ} (hSnon : S.Nonempty) (hSbdd : BddBelow S) :
    sInf ((fun x : ℝ => 2*x) '' S) = 2*sInf S := by
  have himageNon : ((fun x : ℝ => 2*x) '' S).Nonempty := Set.image_nonempty.mpr hSnon
  have hlower : 2*sInf S ∈ lowerBounds ((fun x : ℝ => 2*x) '' S) := by
    intro y hy
    rcases hy with ⟨x,hx,rfl⟩
    exact mul_le_mul_of_nonneg_left (csInf_le hSbdd hx) (by norm_num)
  have hgreat : ∀ z, z ∈ lowerBounds ((fun x : ℝ => 2*x) '' S) → z ≤ 2*sInf S := by
    intro z hz
    have hz' : z/2 ∈ lowerBounds S := by
      intro x hx
      apply (div_le_iff₀ (by norm_num : (0:ℝ)<2)).2
      have hx' : 2*x ∈ (fun x : ℝ => 2*x) '' S := ⟨x,hx,rfl⟩
      have hzx := hz hx'
      nlinarith
    have hInf := le_csInf hSnon (by
      intro x hx
      exact hz' hx)
    nlinarith
  exact (show IsGLB ((fun x : ℝ => 2*x) '' S) (2*sInf S) from ⟨hlower,hgreat⟩).csInf_eq himageNon

 theorem responseFrameEnergyValueSet_eq_image_two_muValueSet (hU : MeasurableSet U)
    (P : BlockVec 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient U) :
    responseFrameEnergyValueSet P ν σ k =
      (fun e : ℝ => 2*e) '' muValueSet U P (responseFramePlanarCoefficientField ν σ k) := by
  ext e
  constructor
  · rintro ⟨X,hX,rfl⟩
    refine ⟨volumeAverage U (blockEnergyDensity (responseFramePlanarCoefficientField ν σ k) X),
      muValueSet_mem hX, ?_⟩
    have havg : volumeAverage U (fun x =>
        responseFrameEnergyDensity ν σ (responseCoefficientExtension k x) (X.eval x)) =
        2 * volumeAverage U (blockEnergyDensity (responseFramePlanarCoefficientField ν σ k) X) := by
      calc
        volumeAverage U (fun x => responseFrameEnergyDensity ν σ
            (responseCoefficientExtension k x) (X.eval x)) =
            volumeAverage U ((2:ℝ) • blockEnergyDensity
              (responseFramePlanarCoefficientField ν σ k) X) := by
                congr 1
                funext x
                rw [responseFrameEnergyDensity_eq_twice_blockEnergyDensity ν σ hν hσ k X x]
                simp [smul_eq_mul]
        _ = 2 * volumeAverage U (blockEnergyDensity
              (responseFramePlanarCoefficientField ν σ k) X) :=
                volumeAverage_smul U (2:ℝ)
                  (blockEnergyDensity (responseFramePlanarCoefficientField ν σ k) X)
    exact havg.symm
  · rintro ⟨m,⟨X,hX,rfl⟩,rfl⟩
    refine ⟨X,hX,?_⟩
    have havg : volumeAverage U (fun x =>
        responseFrameEnergyDensity ν σ (responseCoefficientExtension k x) (X.eval x)) =
        2 * volumeAverage U (blockEnergyDensity (responseFramePlanarCoefficientField ν σ k) X) := by
      calc
        volumeAverage U (fun x => responseFrameEnergyDensity ν σ
            (responseCoefficientExtension k x) (X.eval x)) =
            volumeAverage U ((2:ℝ) • blockEnergyDensity
              (responseFramePlanarCoefficientField ν σ k) X) := by
                congr 1
                funext x
                rw [responseFrameEnergyDensity_eq_twice_blockEnergyDensity ν σ hν hσ k X x]
                simp [smul_eq_mul]
        _ = 2 * volumeAverage U (blockEnergyDensity
              (responseFramePlanarCoefficientField ν σ k) X) :=
                volumeAverage_smul U (2:ℝ)
                  (blockEnergyDensity (responseFramePlanarCoefficientField ν σ k) X)
    exact havg.symm

 theorem responseFrameEnergyValueSet_nonneg (hU : MeasurableSet U)
    (P : BlockVec 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient U) {e : ℝ} (he : e ∈ responseFrameEnergyValueSet P ν σ k) :
    0 ≤ e := by
  rcases he with ⟨X,hX,rfl⟩
  apply volumeAverage_nonneg_of_nonneg_on hU
  intro x hx
  unfold responseFrameEnergyDensity
  apply add_nonneg
  · exact mul_nonneg (div_nonneg hν.le hσ.le) (vecNormSq_nonneg (X.eval x).1)
  · exact mul_nonneg (div_nonneg hσ.le hν.le)
      (vecNormSq_nonneg ((X.eval x).2-(responseCoefficientExtension k x/σ) •
        matVecMul responsePlanarJ (X.eval x).1))

 theorem responseFrameEnergyObservable_eq_sInf_energyValues (hU : IsOpenBoundedConvexDomain U)
    (hvol : 0 < (volume U).toReal) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (P : BlockVec 2) (k : ResponseCoefficient U) :
    responseFrameEnergyObservable hU.isOpen.measurableSet hvol ν σ hν hσ P k =
      sInf (responseFrameEnergyValueSet P ν σ k) := by
  let a := responseFramePlanarCoefficientField ν σ k
  have hEll := responseFramePlanarCoefficientField_isElliptic hU.isOpen.measurableSet ν σ hν hσ k
  have hValues := responseFrameEnergyValueSet_eq_image_two_muValueSet
    hU.isOpen.measurableSet P ν σ hν hσ k
  have hSnon : (muValueSet U P a).Nonempty := muValueSet_nonempty U P a
  have hSbdd : BddBelow (muValueSet U P a) := by
    refine ⟨0, ?_⟩
    intro e he
    have hfull : 2*e ∈ responseFrameEnergyValueSet P ν σ k := by
      rw [hValues]
      exact ⟨e,he,rfl⟩
    have hnonneg := responseFrameEnergyValueSet_nonneg hU.isOpen.measurableSet P ν σ hν hσ k hfull
    nlinarith
  have hImageInf : sInf ((fun e : ℝ => 2*e) '' muValueSet U P a) =
      2 * sInf (muValueSet U P a) := sInf_image_mul_two hSnon hSbdd
  have hObs : responseFrameEnergyObservable hU.isOpen.measurableSet hvol ν σ hν hσ P k =
      2 * Mu U P a := by
    rw [lemmaV_observable_eq_twice_muCandidate]
    rw [← lemmaV_responseSystem_eq_canonical hU.isOpen.measurableSet hvol ν σ hν hσ k]
    have hcan := lemmaV_canonical_muCandidate_eq_Mu hU hEll hvol P
    simpa [a] using congrArg (fun z : ℝ => 2*z) hcan
  rw [hObs, Mu, hValues]
  exact hImageInf.symm

/-- Pointwise localized perturbation in fixed physical units. -/
def localizedPerturbedField (hU : IsOpenBoundedConvexDomain U) (P : BlockVec 2)
    (I : H1Function U →ₗ[ℝ] H1Function U) (η : H1Function U) (ε σ : ℝ)
    (Z : LocalizedAdmissibleState U P) : BlockState 2 where
  potential := Z.field.potential
  flux x := Z.flux x-(ε/σ) • lemmaVPlanarRowField I η (lemmaVAffinePotential hU P.1 Z.correction) x

 theorem localizedShear_energy_identity (hU : IsOpenBoundedConvexDomain U) (P : BlockVec 2)
    (I : H1Function U →ₗ[ℝ] H1Function U) (η : H1Function U)
    (hη : MemLp η.toFun ⊤ (volume.restrict U))
    (hDη : ∀ i, MemLp (fun x => η.grad x i) ⊤ (volume.restrict U))
    (hres : ∀ r : H10Function U, MemH10 U (lemmaVAffinePotential hU P.1 r-I (lemmaVAffinePotential hU P.1 r)).toFun)
    (ν ε σ : ℝ) (k : Vec 2 → ℝ) (Z : LocalizedAdmissibleState U P) (x : Vec 2) :
    responseFrameEnergyDensity ν σ (k x+ε*η.toFun x)
      ((localizedAdmissibleShear hU P I η hη hDη hres ε σ Z).field.eval x) =
    responseFrameEnergyDensity ν σ (k x) ((localizedPerturbedField hU P I η ε σ Z).eval x) := by
  rw [responseFrameEnergyDensity_shear, localizedAdmissibleShear_composition]
  congr 1


/-- Equality of actual energy-value sets; sInf therefore gives the same minimum.
No existence or trial-minimality conclusion has been added as a premise. -/
theorem localizedShear_energy_values (hU : IsOpenBoundedConvexDomain U) (P : BlockVec 2)
    (I : H1Function U →ₗ[ℝ] H1Function U) (η : H1Function U)
    (hη : MemLp η.toFun ⊤ (volume.restrict U))
    (hDη : ∀ i, MemLp (fun x => η.grad x i) ⊤ (volume.restrict U))
    (hres : ∀ r : H10Function U, MemH10 U (lemmaVAffinePotential hU P.1 r-I (lemmaVAffinePotential hU P.1 r)).toFun)
    (ν ε σ : ℝ) (k : Vec 2 → ℝ) :
    {e : ℝ | ∃ X : BlockState 2, IsBlockMuAdmissible U P X ∧ e = volumeAverage U
      (fun x => responseFrameEnergyDensity ν σ (k x+ε*η.toFun x) (X.eval x))} =
    Set.range (fun Z : LocalizedAdmissibleState U P => volumeAverage U
      (fun x => responseFrameEnergyDensity ν σ (k x) ((localizedPerturbedField hU P I η ε σ Z).eval x))) := by
  rw [localizedAdmissibleState_energy_range]
  let T := localizedAdmissibleShearEquiv hU P I η hη hDη hres ε σ
  have he (Z : LocalizedAdmissibleState U P) := congrArg (volumeAverage U)
    (funext (localizedShear_energy_identity hU P I η hη hDη hres ν ε σ k Z))
  have hf : (fun Z : LocalizedAdmissibleState U P => volumeAverage U
      (fun x => responseFrameEnergyDensity ν σ (k x+ε*η.toFun x) (Z.field.eval x))) ∘ T =
      fun Z : LocalizedAdmissibleState U P => volumeAverage U
        (fun x => responseFrameEnergyDensity ν σ (k x) ((localizedPerturbedField hU P I η ε σ Z).eval x)) :=
    funext he
  have hr := T.surjective.range_comp (fun Z : LocalizedAdmissibleState U P => volumeAverage U
    (fun x => responseFrameEnergyDensity ν σ (k x+ε*η.toFun x) (Z.field.eval x)))
  rw [hf] at hr
  exact hr.symm

 theorem localizedShear_response_minimum (hU : IsOpenBoundedConvexDomain U) (P : BlockVec 2)
    (I : H1Function U →ₗ[ℝ] H1Function U) (η : H1Function U)
    (hη : MemLp η.toFun ⊤ (volume.restrict U))
    (hDη : ∀ i, MemLp (fun x => η.grad x i) ⊤ (volume.restrict U))
    (hres : ∀ r : H10Function U, MemH10 U
      (lemmaVAffinePotential hU P.1 r-I (lemmaVAffinePotential hU P.1 r)).toFun)
    (ν ε σ : ℝ) (k : Vec 2 → ℝ) :
    sInf {e : ℝ | ∃ X : BlockState 2, IsBlockMuAdmissible U P X ∧
      e = volumeAverage U (fun x => responseFrameEnergyDensity ν σ
        (k x+ε*η.toFun x) (X.eval x))} =
    sInf (Set.range (fun Z : LocalizedAdmissibleState U P => volumeAverage U
      (fun x => responseFrameEnergyDensity ν σ (k x)
        ((localizedPerturbedField hU P I η ε σ Z).eval x)))) := by
  exact congrArg sInf (localizedShear_energy_values hU P I η hη hDη hres ν ε σ k)

end
end ASDExplicitGamma.Variational
