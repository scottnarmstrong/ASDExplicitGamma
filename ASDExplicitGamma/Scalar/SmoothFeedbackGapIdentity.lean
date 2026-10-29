module

public import ASDExplicitGamma.Scalar.DualMaximizer
public import ASDExplicitGamma.Scalar.DualityStep
public import ASDExplicitGamma.Native.OldSignedEnergyPairingAlgebra
public import ASDExplicitGamma.Native.OldSignedLocalData

/-! The exact actual-source energy identity for the global OLD maximizer.

This is the first pathwise identity in SC-SMOOTH-FEEDBACK-GAP. It uses the
literal scalar source maximizer and an admissible lifted variation; it does
not assume the projection-gap estimate that follows it. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization Response Triadic Variational
open ASDExplicitGamma.Native

noncomputable section

private theorem scalar_field_energy_eq_old_signed_pairing
    (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (F : Vec 2 → BlockVec 2) :
    scalarFieldEnergy ν σ k F = oldSignedEnergyPairing Q ν σ k F F := by
  unfold scalarFieldEnergy oldSignedEnergyPairing
  apply congrArg (volumeAverage (openCubeSet Q))
  funext x
  rw [responseFrameEnergyDensity_eq_scaledCoefficientBlock ν σ
    (responseCoefficientExtension k x) hν hσ]
  rfl

/-- The actual normalized OLD frame energy is nonnegative on every field. -/
theorem smooth_feedback_scalar_field_energy_nonneg
    (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (F : Vec 2 → BlockVec 2) :
    0 ≤ scalarFieldEnergy ν σ k F := by
  rw [scalar_field_energy_eq_old_signed_pairing Q ν σ hν hσ k]
  unfold oldSignedEnergyPairing
  change 0 ≤ volumeAverage (openCubeSet Q) (fun x =>
    blockVecDot (F x) (scalarCoefficientFlux
      (responseFramePlanarCoefficientField ν σ k) F x))
  exact scalar_coefficient_energy_average_nonneg Q
    (responseFramePlanarCoefficientField ν σ k)
    (responseFramePlanarCoefficientField_isElliptic
      (measurableSet_openCubeSet Q) ν σ hν hσ k) F

private theorem old_signed_pairing_smul_left
    (Q : TriadicCube 2) (ν σ : ℝ) (k : ResponseCoefficient (openCubeSet Q))
    (c : ℝ) (F G : Vec 2 → BlockVec 2) :
    oldSignedEnergyPairing Q ν σ k (c • F) G =
      c * oldSignedEnergyPairing Q ν σ k F G := by
  unfold oldSignedEnergyPairing
  have hpoint : (fun x => blockVecDot ((c • F) x)
      (blockMatVecMul (blockCoeffField
        (responseFramePlanarCoefficientField ν σ k) x) (G x))) =
      c • (fun x => blockVecDot (F x)
        (blockMatVecMul (blockCoeffField
          (responseFramePlanarCoefficientField ν σ k) x) (G x))) := by
    funext x
    simp [blockVecDot_smul_left]
  rw [hpoint, volumeAverage_smul]

private theorem old_signed_pairing_smul_right
    (Q : TriadicCube 2) (ν σ : ℝ) (k : ResponseCoefficient (openCubeSet Q))
    (c : ℝ) (F G : Vec 2 → BlockVec 2) :
    oldSignedEnergyPairing Q ν σ k F (c • G) =
      c * oldSignedEnergyPairing Q ν σ k F G := by
  rw [old_signed_energy_pairing_symm Q ν σ k F (c • G),
    old_signed_pairing_smul_left Q ν σ k c G F,
    old_signed_energy_pairing_symm Q ν σ k G F]

private theorem scalar_source_pairing_add
    (Q : TriadicCube 2) (w : Vec 2 → Vec 2)
    (hw : MemVectorL2 (openCubeSet Q) w)
    {F G : Vec 2 → BlockVec 2}
    (hF : MemBlockL2 (openCubeSet Q) F) (hG : MemBlockL2 (openCubeSet Q) G) :
    scalarSourcePairing (openCubeSet Q) w (F + G) =
      scalarSourcePairing (openCubeSet Q) w F +
        scalarSourcePairing (openCubeSet Q) w G := by
  have hIF : IntegrableOn (fun x => vecDot (w x) (F x).1) (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2 hw
      (memVectorL2_fst_of_memBlockL2 hF)
  have hIG : IntegrableOn (fun x => vecDot (w x) (G x).1) (openCubeSet Q) :=
    integrableOn_vecDot_of_memVectorL2 hw
      (memVectorL2_fst_of_memBlockL2 hG)
  unfold scalarSourcePairing
  have hpoint : (fun x => vecDot (w x) ((F + G) x).1) =
      (fun x => vecDot (w x) (F x).1) +
        (fun x => vecDot (w x) (G x).1) := by
    funext x
    simp [vecDot_add_right]
  rw [hpoint, volumeAverage_add hIF hIG]

/-- A global OLD maximizer satisfies the source Euler equation against every
actual scalar variation. -/
theorem smooth_feedback_maximizer_variation_euler
    (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (w : Vec 2 → Vec 2)
    (hw : MemVectorL2 (openCubeSet Q) w)
    (Z Y : Vec 2 → BlockVec 2)
    (hZ : IsScalarOldMaximizer Q ν σ k w Z)
    (hY : ScalarVariation (openCubeSet Q) Y) :
    scalarSourcePairing (openCubeSet Q) w Y =
      oldSignedEnergyPairing Q ν σ k Z Y := by
  let a := scalarFieldEnergy ν σ k Y
  let b := scalarSourcePairing (openCubeSet Q) w Y -
    oldSignedEnergyPairing Q ν σ k Z Y
  have hpoly : ∀ t : ℝ, 2 * t * b - t ^ 2 * a ≤ 0 := by
    intro t
    let tY : Vec 2 → BlockVec 2 := t • Y
    have htY : ScalarVariation (openCubeSet Q) tY := by
      simpa [tY] using scalar_variation_smul hY t
    have hsum : ScalarVariation (openCubeSet Q) (Z + tY) :=
      scalar_variation_add hZ.1 htY
    have hZmem : MemBlockL2 (openCubeSet Q) Z := hZ.1.1
    have hYmem : MemBlockL2 (openCubeSet Q) Y := hY.1
    have htYmem : MemBlockL2 (openCubeSet Q) tY := by
      simpa [tY] using hYmem.const_smul t
    have hsumMem : MemBlockL2 (openCubeSet Q) (Z + tY) := hZmem.add htYmem
    have hsourceAdd := scalar_source_pairing_add Q w hw hZmem htYmem
    have hsourceScale := scalar_source_pairing_smul (openCubeSet Q) w Y t
    have henergyExpand : scalarFieldEnergy ν σ k (Z + tY) =
        scalarFieldEnergy ν σ k Z +
          2 * t * oldSignedEnergyPairing Q ν σ k Z Y + t ^ 2 * a := by
      dsimp only [a]
      rw [scalar_field_energy_eq_old_signed_pairing Q ν σ hν hσ k,
        scalar_field_energy_eq_old_signed_pairing Q ν σ hν hσ k,
        scalar_field_energy_eq_old_signed_pairing Q ν σ hν hσ k]
      have hleft := old_signed_energy_pairing_add_left Q ν σ hν hσ k
        hZmem htYmem hsumMem
      have hrightZ := old_signed_energy_pairing_add_right Q ν σ hν hσ k
        hZmem hZmem htYmem
      have hrightT := old_signed_energy_pairing_add_right Q ν σ hν hσ k
        htYmem hZmem htYmem
      rw [hleft, hrightZ, hrightT,
        old_signed_pairing_smul_right Q ν σ k t Z Y,
        old_signed_pairing_smul_left Q ν σ k t Y Z,
        old_signed_energy_pairing_symm Q ν σ k Y Z,
        old_signed_pairing_smul_left Q ν σ k t Y,
        old_signed_pairing_smul_right Q ν σ k t Y Y]
      ring
    have hmax := hZ.2 (Z + tY) hsum
    rw [hsourceAdd, hsourceScale, henergyExpand] at hmax
    have hself := scalar_old_maximizer_energy_identity Q ν σ k w Z hZ
    dsimp [a, b]
    nlinarith [hmax, hself]
  have hquadratic : ∀ s : ℝ,
      2 * s * (b + a) - s ^ 2 * a ≤ 2 * (b + a) - a := by
    intro s
    have h := hpoly (s - 1)
    dsimp [a, b] at h ⊢
    nlinarith
  have hstationary := quadratic_maximum_euler a (b + a) hquadratic
  dsimp [a, b] at hstationary
  linarith

/-- The exact pathwise gap identity for the actual global OLD maximizer and
any admissible lifted variation. The later `Gap ≤ G_pair` estimate is a
separate parent-versus-cell argument. -/
theorem smooth_feedback_maximizer_gap_identity
    (Q : TriadicCube 2) (ν σ : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (w : Vec 2 → Vec 2)
    (hw : MemVectorL2 (openCubeSet Q) w)
    (Z Y : Vec 2 → BlockVec 2)
    (hZ : IsScalarOldMaximizer Q ν σ k w Z)
    (hY : ScalarVariation (openCubeSet Q) Y) :
    scalarFieldEnergy ν σ k (Z - Y) =
      scalarFieldEnergy ν σ k Y -
        2 * scalarSourcePairing (openCubeSet Q) w Y +
        scalarFieldEnergy ν σ k Z := by
  have hZmem : MemBlockL2 (openCubeSet Q) Z := hZ.1.1
  have hYmem : MemBlockL2 (openCubeSet Q) Y := hY.1
  have hdiffmem : MemBlockL2 (openCubeSet Q) (Z - Y) := hZmem.sub hYmem
  have hEuler := smooth_feedback_maximizer_variation_euler Q ν σ hν hσ
    k w hw Z Y hZ hY
  rw [scalar_field_energy_eq_old_signed_pairing Q ν σ hν hσ k,
    scalar_field_energy_eq_old_signed_pairing Q ν σ hν hσ k,
    scalar_field_energy_eq_old_signed_pairing Q ν σ hν hσ k]
  have hleft := old_signed_energy_pairing_sub_left Q ν σ hν hσ k
    hZmem hYmem hdiffmem
  have hrightZ := old_signed_energy_pairing_sub_right Q ν σ hν hσ k
    hZmem hZmem hYmem
  have hrightY := old_signed_energy_pairing_sub_right Q ν σ hν hσ k
    hYmem hZmem hYmem
  rw [hleft, hrightZ, hrightY,
    old_signed_energy_pairing_symm Q ν σ k Y Z, hEuler]
  ring

/-- The first Lambda8 identity for the literal finite-cell lift. The source
field `(w,0)` is a genuine parent variation, and the lift is the actual
`oldSignedLocalResidual` assembled from its restrictions to the cells. -/
theorem smooth_feedback_actual_local_lift_gap_identity
    (Q : TriadicCube 2) (depth : ℕ) (ν σ : ℝ)
    (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (w : Vec 2 → Vec 2)
    (hW : ScalarVariation (openCubeSet Q) (fun x => (w x, 0)))
    (Z : Vec 2 → BlockVec 2)
    (hZ : IsScalarOldMaximizer Q ν σ k w Z) :
    let F : Vec 2 → BlockVec 2 := fun x => (w x, 0)
    let Y := oldSignedLocalResidual Q depth ν σ hν hσ k F hW.1
    scalarFieldEnergy ν σ k (Z - Y) =
      scalarFieldEnergy ν σ k Y -
        2 * scalarSourcePairing (openCubeSet Q) w Y +
        scalarFieldEnergy ν σ k Z := by
  classical
  dsimp only
  let F : Vec 2 → BlockVec 2 := fun x => (w x, 0)
  let Y : Vec 2 → BlockVec 2 :=
    oldSignedLocalResidual Q depth ν σ hν hσ k F hW.1
  have hRemoved := old_signed_local_removed_variation Q depth ν σ hν hσ k F hW.1
  have hY : ScalarVariation (openCubeSet Q) Y := by
    have hadd := scalar_variation_add hW (scalar_variation_smul hRemoved (-1 : ℝ))
    have hfields : (fun x => F x + (-1 : ℝ) • (F x - Y x)) = Y := by
      funext x
      ext i <;> simp [F, Y, sub_eq_add_neg]
    rw [← hfields]
    exact hadd
  have hw : MemVectorL2 (openCubeSet Q) w := by
    simpa [F] using memVectorL2_fst_of_memBlockL2 hW.1
  exact smooth_feedback_maximizer_gap_identity Q ν σ hν hσ k w hw Z Y hZ hY

/-- The actual OLD maximizer energy is bounded by the finite patch of local
bottom-source solves. This is the duality half of the Λ8 gap estimate; the
cellwise history split of this patch is a separate estimate. -/
theorem smooth_feedback_actual_bottom_local_dual_bound
    (Q : TriadicCube 2) (depth : ℕ) (ν σ : ℝ)
    (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (w : Vec 2 → Vec 2)
    (hw : MemVectorL2 (openCubeSet Q) w)
    (Z : Vec 2 → BlockVec 2)
    (hZ : IsScalarOldMaximizer Q ν σ k w Z) :
    scalarFieldEnergy ν σ k Z ≤
      scalarFieldEnergy ν σ k
        (oldSignedLocalResidual Q depth ν σ hν hσ k
          (scalarBottomLoad w) (scalar_bottom_load_memL2 hw)) := by
  classical
  let F : Vec 2 → BlockVec 2 := scalarBottomLoad w
  let Y : Vec 2 → BlockVec 2 := oldSignedLocalResidual Q depth ν σ hν hσ k
    F (scalar_bottom_load_memL2 hw)
  have hRemoved := old_signed_local_removed_variation Q depth ν σ hν hσ k
    F (scalar_bottom_load_memL2 hw)
  have hPatchVariation : ScalarVariation (openCubeSet Q) (Y - F) := by
    have hneg := scalar_variation_smul hRemoved (-1 : ℝ)
    have hfields : (fun x => (-1 : ℝ) • (F x - Y x)) = Y - F := by
      funext x
      apply Prod.ext
      · funext i
        change (-1 : ℝ) * ((F x).1 i - (Y x).1 i) =
          (Y x).1 i - (F x).1 i
        ring
      · funext i
        change (-1 : ℝ) * ((F x).2 i - (Y x).2 i) =
          (Y x).2 i - (F x).2 i
        ring
    change ScalarVariation (openCubeSet Q)
      (fun x => (-1 : ℝ) • (F x - Y x)) at hneg
    rw [hfields] at hneg
    exact hneg
  have hCompatible : ScalarCompatible (openCubeSet Q) (Y - F) :=
    scalar_variation_compatible hPatchVariation
  have hBound := scalar_old_maximizer_duality_bound Q ν σ hν hσ k w hw Z
    (Y - F) hZ hCompatible
  have hPatch : scalarBottomLoad w + (Y - F) = Y := by
    funext x
    ext i <;> simp [F, scalarBottomLoad, sub_eq_add_neg]
  rw [hPatch] at hBound
  simpa [Y, F] using hBound

/-- Before history estimates, the actual global gap is controlled by the
literal top-source lift and bottom-source dual patch. This is the pathwise
duality comparison from which `Gap ≤ G_pair` is assembled. -/
theorem smooth_feedback_actual_two_patch_gap_bound
    (Q : TriadicCube 2) (depth : ℕ) (ν σ : ℝ)
    (hν : 0 < ν) (hσ : 0 < σ)
    (k : ResponseCoefficient (openCubeSet Q)) (w : Vec 2 → Vec 2)
    (hW : ScalarVariation (openCubeSet Q) (fun x => (w x, 0)))
    (Z : Vec 2 → BlockVec 2)
    (hZ : IsScalarOldMaximizer Q ν σ k w Z) :
    let hw := memVectorL2_fst_of_memBlockL2 hW.1
    let Ftop : Vec 2 → BlockVec 2 := fun x => (w x, 0)
    let Ytop := oldSignedLocalResidual Q depth ν σ hν hσ k Ftop hW.1
    let Ybottom := oldSignedLocalResidual Q depth ν σ hν hσ k
      (scalarBottomLoad w) (scalar_bottom_load_memL2 hw)
    scalarFieldEnergy ν σ k (Z - Ytop) ≤
      scalarFieldEnergy ν σ k Ytop -
        2 * scalarSourcePairing (openCubeSet Q) w Ytop +
        scalarFieldEnergy ν σ k Ybottom := by
  dsimp only
  let hw : MemVectorL2 (openCubeSet Q) w :=
    memVectorL2_fst_of_memBlockL2 hW.1
  let Ftop : Vec 2 → BlockVec 2 := fun x => (w x, 0)
  let Ytop : Vec 2 → BlockVec 2 :=
    oldSignedLocalResidual Q depth ν σ hν hσ k Ftop hW.1
  let Ybottom : Vec 2 → BlockVec 2 := oldSignedLocalResidual Q depth ν σ hν hσ k
    (scalarBottomLoad w) (scalar_bottom_load_memL2 hw)
  have hIdentity := smooth_feedback_actual_local_lift_gap_identity
    Q depth ν σ hν hσ k w hW Z hZ
  have hDual := smooth_feedback_actual_bottom_local_dual_bound
    Q depth ν σ hν hσ k w hw Z hZ
  rw [hIdentity]
  linarith

end

end ASDExplicitGamma.Scalar
