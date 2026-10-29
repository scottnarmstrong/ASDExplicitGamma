module

public import ASDExplicitGamma.Variational.LocalizedEnergyBounds
public import ASDExplicitGamma.Variational.LocalizedRowAction

/-! Bounded nilpotent localized operators on the actual closed energy carrier. -/

@[expose] public section
namespace ASDExplicitGamma.Variational
open Homogenization MeasureTheory ASDExplicitGamma.Response
noncomputable section

local instance localizedEnergyFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

 theorem localizedEnergyPureSecond_norm_sq (Q : TriadicCube 2)
    (hU : MeasurableSet (openCubeSet Q)) (hvol : 0 < (volume (openCubeSet Q)).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (k : ResponseCoefficient (openCubeSet Q))
    (Y : HilbertVectorL2 (openCubeSet Q)) :
    ‖localizedEnergyPureSecond Q
      (responseFrameEnergyData hU hvol ν σ hν hσ k) Y‖^2 =
      (volume (openCubeSet Q)).toReal⁻¹ * (σ/ν) * ‖Y‖^2 := by
  change ‖responseEnergyUpCLM (responseFrameEnergyData hU hvol ν σ hν hσ k)
    (hilbertPureSecondL2 (openCubeSet Q) Y)‖^2 = _
  rw [responseEnergyUpCLM_apply]
  rw [energyCarrier_norm_sq (responseFrameEnergyData hU hvol ν σ hν hσ k)
    (responseEnergyUp (responseFrameEnergyData hU hvol ν σ hν hσ k)
      (hilbertPureSecondL2 (openCubeSet Q) Y))]
  rw [responseEnergyUp_down]
  exact hilbertPureSecond_energy_eq hU hvol ν σ hν hσ k Y

 theorem localizedEnergyFirst_energy_bound (Q : TriadicCube 2)
    (hU : MeasurableSet (openCubeSet Q)) (hvol : 0 < (volume (openCubeSet Q)).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (k : ResponseCoefficient (openCubeSet Q))
    (X : localizedEnergyClosedSubmodule Q
      (responseFrameEnergyData hU hvol ν σ hν hσ k)) :
    (ν/σ) * ‖localizedEnergyFirst Q
      (responseFrameEnergyData hU hvol ν σ hν hσ k) X‖^2 ≤
      (volume (openCubeSet Q)).toReal * ‖X‖^2 := by
  let D := responseFrameEnergyData hU hvol ν σ hν hσ k
  have h := hilbertFirstProjection_energy_bound hU hvol ν σ hν hσ k
    (responseEnergyDownCLM D X.1)
  rw [responseEnergyDownCLM_apply] at h
  rw [← energyCarrier_norm_sq D X.1] at h
  change (ν/σ) * ‖(hilbertFirstProjection (openCubeSet Q))
      (responseEnergyDownCLM D X.1)‖^2 ≤ (volume (openCubeSet Q)).toReal * ‖X‖^2 at h
  change (ν/σ) * ‖(hilbertFirstProjection (openCubeSet Q))
      (responseEnergyDownCLM D X.1)‖^2 ≤ _
  exact h

 def localizedEnergyOperator (Q : TriadicCube 2)
    (D : EnergyHilbertData (H := HilbertBlockL2 (openCubeSet Q))) (σ : ℝ)
    (R : affineGradientClosedSubmodule Q →L[ℝ] HilbertVectorL2 (openCubeSet Q)) :
    localizedEnergyClosedSubmodule Q D →L[ℝ] localizedEnergyClosedSubmodule Q D :=
  (-(1/σ) • localizedEnergyPureSecond Q D).comp (R.comp (localizedEnergyFirst Q D))

 theorem localizedEnergyOperator_norm_le (Q : TriadicCube 2)
    (hU : MeasurableSet (openCubeSet Q)) (hvol : 0 < (volume (openCubeSet Q)).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (k : ResponseCoefficient (openCubeSet Q))
    (R : affineGradientClosedSubmodule Q →L[ℝ] HilbertVectorL2 (openCubeSet Q)) :
    ‖localizedEnergyOperator Q (responseFrameEnergyData hU hvol ν σ hν hσ k) σ R‖ ≤ ‖R‖/ν := by
  let D := responseFrameEnergyData hU hvol ν σ hν hσ k
  let α : ℝ := (1/σ)^2 * ((volume (openCubeSet Q)).toReal⁻¹ * (σ/ν))
  have hα : 0 ≤ α := by positivity
  refine ContinuousLinearMap.opNorm_le_bound _ (div_nonneg (norm_nonneg R) hν.le) ?_
  intro X
  let G := localizedEnergyFirst Q D X
  have hpoint : ‖localizedEnergyOperator Q D σ R X‖^2 =
      α * ‖R G‖^2 := by
    rw [localizedEnergyOperator, ContinuousLinearMap.comp_apply, smul_apply,
      norm_smul]
    have hc : ‖-(1/σ : ℝ)‖ = 1/σ := by
      rw [norm_neg, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hσ)]
    rw [hc, mul_pow, localizedEnergyPureSecond_norm_sq Q hU hvol ν σ hν hσ k]
    dsimp [G, α]
    ring
  have hR : ‖R G‖^2 ≤ ‖R‖^2 * ‖G‖^2 := by
    have h := R.le_opNorm G
    nlinarith [norm_nonneg (R G), norm_nonneg R, norm_nonneg G]
  have hG := localizedEnergyFirst_energy_bound Q hU hvol ν σ hν hσ k X
  have hG0 : (ν/σ) * ‖G‖^2 ≤ (volume (openCubeSet Q)).toReal * ‖X‖^2 := by
    change (ν/σ) * ‖G‖^2 ≤ _ at hG
    exact hG
  have hG' : ‖G‖^2 ≤ (volume (openCubeSet Q)).toReal * (σ/ν) * ‖X‖^2 := by
    have hs := mul_le_mul_of_nonneg_left hG0 (div_nonneg hσ.le hν.le)
    have hc : (σ/ν)*(ν/σ)=1 := by field_simp [hν.ne', hσ.ne']
    calc
      ‖G‖^2 = (σ/ν)*(ν/σ)*‖G‖^2 := by rw [hc]; ring
      _ ≤ (σ/ν)*((volume (openCubeSet Q)).toReal*‖X‖^2) := by
        simpa only [← mul_assoc] using hs
      _ = (volume (openCubeSet Q)).toReal*(σ/ν)*‖X‖^2 := by ring
  have hsq : ‖localizedEnergyOperator Q D σ R X‖^2 ≤ (‖R‖/ν)^2*‖X‖^2 := by
    rw [hpoint]
    calc
      α*‖R G‖^2 ≤ α*(‖R‖^2*‖G‖^2) := mul_le_mul_of_nonneg_left hR hα
      _ ≤ α*(‖R‖^2*((volume (openCubeSet Q)).toReal*(σ/ν)*‖X‖^2)) := by
        gcongr
      _ = (‖R‖/ν)^2*‖X‖^2 := by
        dsimp [α]
        field_simp [hν.ne', hσ.ne', hvol.ne']
  have hb : 0 ≤ ‖R‖/ν := div_nonneg (norm_nonneg R) hν.le
  have hx : 0 ≤ ‖X‖ := norm_nonneg X
  exact (sq_le_sq₀ (norm_nonneg (localizedEnergyOperator Q D σ R X))
    (mul_nonneg hb hx)).mp (by simpa only [mul_pow] using hsq)

 theorem localizedEnergyOperator_row_norm_le (Q : TriadicCube 2)
    (hU : MeasurableSet (openCubeSet Q)) (hvol : 0 < (volume (openCubeSet Q)).toReal)
    (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ) (k : ResponseCoefficient (openCubeSet Q))
    (I : H1Function (openCubeSet Q) →ₗ[ℝ] H1Function (openCubeSet Q))
    (η : H1Function (openCubeSet Q))
    (hη : MemLp η.toFun ⊤ (volume.restrict (openCubeSet Q)))
    (hDη : ∀ i, MemLp (fun x => η.grad x i) ⊤ (volume.restrict (openCubeSet Q)))
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hI : ∀ v ∈ affinePotentialSubmodule Q,
      ‖(I v).gradToHilbertVectorL2‖ ≤ A*‖v.gradToHilbertVectorL2‖)
    (hR : ∀ v ∈ affinePotentialSubmodule Q,
      ‖(v-I v).toScalarL2‖ ≤ B*‖v.gradToHilbertVectorL2‖) :
    ‖localizedEnergyOperator Q (responseFrameEnergyData hU hvol ν σ hν hσ k) σ
      (localizedRowOperator Q I η hη hDη hA hB hI hR)‖ ≤
      (A*‖hη.toLp η.toFun‖+B*‖weakColumnDivergenceLp η hDη‖)/ν := by
  calc
    _ ≤ ‖localizedRowOperator Q I η hη hDη hA hB hI hR‖/ν :=
      localizedEnergyOperator_norm_le Q hU hvol ν σ hν hσ k _
    _ ≤ (A*‖hη.toLp η.toFun‖+B*‖weakColumnDivergenceLp η hDη‖)/ν := by
      apply div_le_div_of_nonneg_right
        (localizedRowOperator_norm_le Q I η hη hDη hA hB hI hR) hν.le

 theorem localizedEnergyOperator_pairwise_nilpotent (Q : TriadicCube 2)
    (D : EnergyHilbertData (H := HilbertBlockL2 (openCubeSet Q))) (σ : ℝ)
    (R S : affineGradientClosedSubmodule Q →L[ℝ] HilbertVectorL2 (openCubeSet Q)) :
    (localizedEnergyOperator Q D σ R).comp (localizedEnergyOperator Q D σ S)=0 := by
  apply ContinuousLinearMap.ext
  intro X
  simp only [localizedEnergyOperator, ContinuousLinearMap.comp_apply, smul_apply,
    map_smul, localizedEnergyFirst_pureSecond, smul_zero, map_zero, zero_apply]

end
end ASDExplicitGamma.Variational
