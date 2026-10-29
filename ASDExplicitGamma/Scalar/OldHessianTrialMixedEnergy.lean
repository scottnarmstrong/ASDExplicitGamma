module

public import ASDExplicitGamma.Scalar.OldHessianTrialCenteredMixedEnergy
public import ASDExplicitGamma.Scalar.OldHessianTrialProjectedSource

/-! Complete full mixed-source and actual projected R energies. The source
row and retained coarse product are summed before any random bank payment. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Native Response Triadic Variational Gaussian Inverse Main
noncomputable section
attribute [local irreducible] Homogenization.descendantsAtDepth

theorem old_hessian_source_multiplier_nonneg (Q : TriadicCube 2) (fine : ℕ)
    (b : ℝ) (L : {l : ℝ // 0<l}) : 0≤oldSignedSourceMultiplier Q fine b L := by
  have hr := (diagMeshRadius_pos Q fine).le
  unfold oldSignedSourceMultiplier
  positivity

/-- The full actual mixed source has its complete positive-energy bound,
with the fine row and genuine coarse product coefficients kept separate. -/
theorem old_hessian_actual_mixed_source_energy (n : ℤ) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet (originCube 2 n))) (b : ℝ) (L : {l : ℝ // 0<l}) (i : Fin 2) :
    let Q := originCube 2 n
    let u := oldHessianMixedPotential Q coarse nu sigma hnu hsigma k i
    let E := fun j : whiteBasisIndex => oldHessianBrokenColumnEnergy Q (coarse+1)
      (fun _U x => (oldHessianMixedBottomSource Q coarse (coarse+1) nu sigma hnu hsigma k b L j i x).2)
    Summable E ∧ Real.sqrt (∑' j,E j) ≤
      oldSignedSourceMultiplier Q (coarse+1) b L*
        Real.sqrt (lemmaVTiledWeakEnergy Q (coarse+1) u.toH1Function.grad)+
      Real.sqrt (oldHessianCoarseColumnBill Q coarse nu sigma hnu hsigma k (basisVec i) b L) := by
  intro Q u E
  let phi := oldHessianCoarsePotential Q coarse nu sigma hnu hsigma k (basisVec i)
  let F := fun (j : whiteBasisIndex) (_U : TriadicCube 2) =>
    lemmaVPlanarRowField (diagInterpolant Q (coarse+1))
      (mainQ3DirectionW2 Q b L (whiteBasis j)).value u.toH1Function
  let G := fun (j : whiteBasisIndex) (_U : TriadicCube 2) => oldHessianCoarseProduct Q b L phi (whiteBasis j)
  have hFm (j : whiteBasisIndex) (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q (coarse+1))
      (r : Fin 2) : MemLp (fun x => F j U x r) 2 (normalizedCubeMeasure U) := by
    have hm := old_signed_localized_potential_shear_memL2 Q (diagInterpolant Q (coarse+1))
      (mainQ3DirectionW2 Q b L (whiteBasis j)).value u.toH1Function
      (mainQ3DirectionW2 Q b L (whiteBasis j)).value_memLp_top
      (mainQ3DirectionW2 Q b L (whiteBasis j)).gradient_memLp_top_volume
    have hu := hm.mono_measure (Measure.restrict_mono_set volume (openCubeSet_subset_of_mem_descendantsAtDepth hU))
    have hn := (memLp_normalized_of_memL2On (memScalarL2_coord_of_memVectorL2 (memVectorL2_snd_of_memBlockL2 hu) r)).neg
    change MemLp (fun x => -(-lemmaVPlanarRowField (diagInterpolant Q (coarse+1))
      (mainQ3DirectionW2 Q b L (whiteBasis j)).value u.toH1Function x r)) 2 (normalizedCubeMeasure U) at hn
    simpa only [neg_neg] using hn
  have hFp (j : whiteBasisIndex) (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q (coarse+1))
      (r : Fin 2) : Summable (fun d => (Real.sqrt 3)^(d+1)*energy U
        (cubeIncrement U (d+1) (fun x => F j U x r))) := by
    simpa only [oldSignedLocalizedPotentialShear,Pi.neg_apply,cubeIncrement_neg,energy_neg] using
      old_hessian_localized_row_positive n (coarse+1) b L u U hU j r
  have hGm (j : whiteBasisIndex) (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q (coarse+1))
      (r : Fin 2) := (old_hessian_coarse_product_regular Q (coarse+1) b L phi j U hU r).1
  have hGp (j : whiteBasisIndex) (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q (coarse+1))
      (r : Fin 2) := (old_hessian_coarse_product_regular Q (coarse+1) b L phi j U hU r).2
  have hrow := old_hessian_localized_row_energy n (coarse+1) b L u
  have heF (j : whiteBasisIndex) : oldHessianBrokenColumnEnergy Q (coarse+1) (F j)=
      descendantsAverage Q (coarse+1) (fun U => vectorPositiveHaarEnergy U (fun x =>
        (oldSignedLocalizedPotentialShear (diagInterpolant Q (coarse+1))
          (mainQ3DirectionW2 Q b L (whiteBasis j)).value u.toH1Function x).2)) := by
    simp only [oldHessianBrokenColumnEnergy,oldSignedLocalizedPotentialShear,
      vectorPositiveHaarEnergy,Pi.neg_apply,primalEnergy_neg]
    rfl
  have hFs : Summable (fun j => oldHessianBrokenColumnEnergy Q (coarse+1) (F j)) :=
    hrow.1.congr (fun j => (heF j).symm)
  have hprod := old_hessian_patched_product_energy Q coarse nu sigma hnu hsigma k (basisVec i) b L
  have hGs : Summable (fun j => oldHessianBrokenColumnEnergy Q (coarse+1) (G j)) := hprod.1
  have ht := old_hessian_broken_cell_positive_triangle Q (coarse+1) F G hFm hGm hFp hGp hFs hGs
  have he (j : whiteBasisIndex) : E j=oldHessianBrokenColumnEnergy Q (coarse+1)
      (fun U x r => F j U x r+G j U x r) := by
    unfold oldHessianBrokenColumnEnergy
    apply congrArg (descendantsAverage Q (coarse+1))
    funext U
    dsimp only
    have hs (x : Vec 2) : (oldHessianMixedBottomSource Q coarse (coarse+1)
        nu sigma hnu hsigma k b L j i x).2=-(F j U x+G j U x) := by
      change -F j U x + -G j U x=-(F j U x+G j U x)
      abel
    simp_rw [hs]
    simp only [vectorPositiveHaarEnergy,Pi.neg_apply,Pi.add_apply,primalEnergy_neg]
  simp_rw [←he] at ht
  have hrowB := Real.sqrt_le_sqrt hrow.2
  rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (old_hessian_source_multiplier_nonneg Q (coarse+1) b L)] at hrowB
  have hrowBound : Real.sqrt (∑' j,oldHessianBrokenColumnEnergy Q (coarse+1) (F j)) ≤
      oldSignedSourceMultiplier Q (coarse+1) b L*Real.sqrt (lemmaVTiledWeakEnergy Q (coarse+1) u.toH1Function.grad) := by
    simpa only [heF] using hrowB
  exact ⟨ht.1,ht.2.trans (add_le_add hrowBound (Real.sqrt_le_sqrt hprod.2))⟩

/-- The actual fine projected mixed residual has a complete energy series
and the physical one-bank source-square bound, without a source estimate premise. -/
theorem old_hessian_actual_mixed_residual_energy (n : ℤ) (coarse : ℕ)
    (nu sigma : ℝ) (hnu : 0<nu) (hsigma : 0<sigma)
    (k : ResponseCoefficient (openCubeSet (originCube 2 n))) (b : ℝ) (L : {l : ℝ // 0<l}) (i : Fin 2) :
    let Q := originCube 2 n
    let u := oldHessianMixedPotential Q coarse nu sigma hnu hsigma k i
    let R := fun j => oldHessianMixedBottomResidual Q coarse (coarse+1) nu sigma hnu hsigma k b L j i
    let C := oldSignedSourceMultiplier Q (coarse+1) b L*
      Real.sqrt (lemmaVTiledWeakEnergy Q (coarse+1) u.toH1Function.grad)+
      Real.sqrt (oldHessianCoarseColumnBill Q coarse nu sigma hnu hsigma k (basisVec i) b L)
    Summable (fun j => oldSignedEnergyPairing Q nu sigma k (R j) (R j)) ∧
      (∑' j,oldSignedEnergyPairing Q nu sigma k (R j) (R j)) ≤
        oldHessianFineInverseHistory Q (coarse+1) nu sigma k*C^2 := by
  intro Q u R C
  let E := fun j : whiteBasisIndex => oldHessianBrokenColumnEnergy Q (coarse+1)
    (fun _U x => (oldHessianMixedBottomSource Q coarse (coarse+1) nu sigma hnu hsigma k b L j i x).2)
  let B := oldHessianFineInverseHistory Q (coarse+1) nu sigma k
  have hs := old_hessian_actual_mixed_source_energy n coarse nu sigma hnu hsigma k b L i
  have hn (j : whiteBasisIndex) : 0≤E j := old_hessian_broken_column_energy_nonneg Q (coarse+1) _
  have hC : 0≤C := add_nonneg (mul_nonneg (old_hessian_source_multiplier_nonneg Q (coarse+1) b L)
    (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hcap := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs.2 2
  rw [Real.sq_sqrt (tsum_nonneg hn)] at hcap
  have hp (j : whiteBasisIndex) : oldSignedEnergyPairing Q nu sigma k (R j) (R j)≤B*E j :=
    old_hessian_actual_mixed_projection_energy n coarse (coarse+1) nu sigma hnu hsigma k b L j i
  have hR := (hs.1.mul_left B).of_nonneg_of_le
    (fun j => old_signed_energy_pairing_nonneg Q nu sigma hnu hsigma k _) hp
  refine ⟨hR,?_⟩
  have hh := hR.tsum_le_tsum hp (hs.1.mul_left B)
  rw [tsum_mul_left] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hcap (old_hessian_fine_history_nonneg Q (coarse+1) nu sigma k))

end
end ASDExplicitGamma.Scalar
