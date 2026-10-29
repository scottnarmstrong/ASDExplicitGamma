module

public import ASDExplicitGamma.Native.OldSignedAffineCorrector
public import ASDExplicitGamma.Native.OldSignedResidualEnergyContraction
public import ASDExplicitGamma.Variational.ForcedSourceFeedback

/-! Sharp OLD pure-second energy and first-potential bounds, with an
explicit identification of the actual L2 load and projected-source load. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Scalar
open ASDExplicitGamma.Variational ASDExplicitGamma.Triadic
noncomputable section

/-- The projected-source load is exactly the physical pure-second input,
as an L2 class, without any representative convention premise. -/
theorem old_signed_pure_second_load_eq (Q : TriadicCube 2) (g : Vec 2 → Vec 2)
    (hg : MemLp g 2 (normalizedCubeMeasure Q))
    (hF : MemBlockL2 (openCubeSet Q) (fun x => (0,g x))) :
    projectedSourceLoad Q hg=toHilbertBlockL2OfBlockField hF := by
  let hgv := memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure Q hg
  apply Lp.ext
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volumeMeasureOn (openCubeSet Q))
    (L := hilbertPureSecond.toContinuousLinearMap) (f := toHilbertVectorL2OfVecField hgv),
    coeFn_toHilbertVectorL2OfVecField hgv,coeFn_toHilbertBlockL2OfBlockField hF]
    with x hpure hvec hfield
  change hilbertPureSecondL2 (openCubeSet Q) (toHilbertVectorL2OfVecField hgv) x=_
  rw [hfield]
  have hh : hilbertPureSecondL2 (openCubeSet Q) (toHilbertVectorL2OfVecField hgv) x=
      hilbertPureSecond.toContinuousLinearMap (hilbertifyVecField g x) := by
    simpa only [hilbertPureSecondL2,hvec] using hpure
  rw [hh]
  apply HilbertBlockVec.ext <;>
    simp [hilbertPureSecond,hilbertifyBlockField,hilbertifyVecField,
      HilbertBlockVec.potential,HilbertBlockVec.flux]

/-- Sharp inverse-history energy bound for the actual weighted residual
of a pure-second physical source. -/
theorem old_signed_pure_second_sharp_energy (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (g : Vec 2 → Vec 2)
    (hF : MemBlockL2 (openCubeSet Q) (fun x => (0,g x)))
    (hp : ∀ i : Fin 2,Summable (fun j : ℕ => (Real.sqrt 3)^(j+1)*energy Q
      (cubeIncrement Q (j+1) (fun x => g x i)))) :
    let R := scalarResidualField Q nu sigma hnu hsigma k (toHilbertBlockL2OfBlockField hF)
    oldSignedEnergyPairing Q nu sigma k R R ≤
      oldSignedInverseHistory Q (responseFramePlanarCoefficientField nu sigma k)*vectorPositiveHaarNorm Q g^2 := by
  intro R
  have hg : MemLp g 2 (normalizedCubeMeasure Q) := memLp_pi_iff.mpr
    (fun i => memLp_normalized_of_memL2On
      (memScalarL2_coord_of_memVectorL2 (memVectorL2_snd_of_memBlockL2 hF) i))
  have hh := projected_source_energy_le_source_history Q nu sigma hnu hsigma k hg hp
  rw [old_signed_pure_second_load_eq Q g hg hF] at hh
  have hR : MemBlockL2 (openCubeSet Q) R := R.property
  have hr : toHilbertBlockL2OfBlockField hR=
      scalarProjectionResidual Q nu sigma hnu hsigma k (toHilbertBlockL2OfBlockField hF) :=
    hilbert_field_rebuild _
  have he := scalar_frame_bilinear_field Q nu sigma hnu hsigma k hR hR
  rw [hr] at he
  rw [he] at hh
  simpa only [oldSignedEnergyPairing,oldSignedInverseHistory,vectorPositiveHaarNorm,
    Real.sq_sqrt (vectorPositiveHaarEnergy_nonneg Q g)] using hh

/-- A genuine zero-boundary first potential of the actual residual has
its derivative feedback norm controlled by the literal OLD inverse history. -/
theorem old_signed_pure_second_sharp_first (Q : TriadicCube 2)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet Q)) (g : Vec 2 → Vec 2)
    (hF : MemBlockL2 (openCubeSet Q) (fun x => (0,g x)))
    (hp : ∀ i : Fin 2,Summable (fun j : ℕ => (Real.sqrt 3)^(j+1)*energy Q
      (cubeIncrement Q (j+1) (fun x => g x i))))
    (v : H10Function (openCubeSet Q))
    (hv : (fun x => (scalarResidualField Q nu sigma hnu hsigma k
      (toHilbertBlockL2OfBlockField hF) x).1) =ᵐ[volumeMeasureOn (openCubeSet Q)] v.toH1Function.grad) :
    vectorWeakHaarNorm Q v.toH1Function.grad ≤
      (1+inverseHistoryDiscount)*oldSignedInverseHistory Q
        (responseFramePlanarCoefficientField nu sigma k)*vectorPositiveHaarNorm Q g := by
  have hg : MemLp g 2 (normalizedCubeMeasure Q) := memLp_pi_iff.mpr
    (fun i => memLp_normalized_of_memL2On
      (memScalarL2_coord_of_memVectorL2 (memVectorL2_snd_of_memBlockL2 hF) i))
  have hv' : (fun x => (projectedSourceField Q nu sigma hnu hsigma k hg x).1) =ᵐ[
      volumeMeasureOn (openCubeSet Q)] v.toH1Function.grad := by
    unfold projectedSourceField
    rw [old_signed_pure_second_load_eq Q g hg hF]
    exact hv
  have hh := projectedSource_forced_feedback_bound Q nu sigma hnu hsigma k hg hp v hv'
  have hB : 0≤oldSignedInverseHistory Q (responseFramePlanarCoefficientField nu sigma k) :=
    lemmaVInverseHistory_nonneg Q _ (Real.one_lt_rpow (by norm_num) (by norm_num))
  have hdiscount : inverseHistoryDiscount=(3:ℝ)^(-(1/4:ℝ)) := by
    rw [inverse_history_discount_eq,←Real.rpow_neg (by norm_num : (0:ℝ)≤3)]
  change vectorWeakHaarNorm Q v.toH1Function.grad ≤
    (1/2+(3:ℝ)^(-(1/4:ℝ)))*oldSignedInverseHistory Q
      (responseFramePlanarCoefficientField nu sigma k)*vectorPositiveHaarNorm Q g at hh
  exact hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by rw [hdiscount]; norm_num) hB) (Real.sqrt_nonneg _))

end
end ASDExplicitGamma.Native
