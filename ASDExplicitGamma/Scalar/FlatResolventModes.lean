module

public import ASDExplicitGamma.Scalar.FlatResolvent
public import ASDExplicitGamma.Scalar.DefectResolventCarriers
public import ASDExplicitGamma.Scalar.PhysicalResolventParity
public import ASDExplicitGamma.Gaussian.RectangleClosure

/-! The flat first-response modes and their actual projected source in the
physical four-term resolvent identity. -/

@[expose] public section

open MeasureTheory Homogenization
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Response ASDExplicitGamma.Triadic
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped InnerProduct ENNReal

namespace ASDExplicitGamma.Scalar

local instance flatResolventModesFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

/-- For the actual cutoff shell and the true annealed frame, the flat first
response is the pure-second injection of the projected source.  Applying the
actual fresh insertion block gives the source's quarter-turn followed by its
physical flux projection.  The mode clause fixes the same sign mode by mode;
the flux projection is retained explicitly. -/
theorem actual_flat_first_response_source_bridge
    (Q : TriadicCube 2) {a₀ b₀ c₀ d₀ : ℝ}
    (hab : a₀ < b₀) (hcd : c₀ < d₀)
    (hQ : openCubeSet Q ⊆ openRectangle a₀ b₀ c₀ d₀)
    (M : ABKModel 2) (h : ℝ) (m : ℤ)
    (ω : Cutoff.CutoffSample 2) (e : Vec 2) :
    let U := openCubeSet Q
    let K := closedRectangle a₀ b₀ c₀ d₀
    let hQcl : closure U ⊆ K := by
      change closure (openCubeSet Q) ⊆ closedRectangle a₀ b₀ c₀ d₀
      rw [← rectangle_closure a₀ b₀ c₀ d₀ hab hcd]
      exact closure_mono hQ
    let hU := measurableSet_openCubeSet Q
    let hvol : 0 < (volume U).toReal := by
      rw [volume_openCubeSet_toReal]
      exact cubeVolume_pos Q
    let ν := M.nu
    let hν : 0 < ν := M.nu_pos
    let σ : ℝ := Annealed.sigmaBar M m
    let hσ : 0 < σ := (Annealed.sigmaBar M m).property
    let β := q3ModelAmplitude M h (m + 1)
    let L := q3ModelLength (m + 1)
    let z := shellFieldScalarRestriction K (ω.1 (m + 1))
    let k := physicalResponseRestriction Q hQcl (olderField K m ω)
    let H := σ • physicalResponseRestriction Q hQcl z
    let p := flatSourcePotentialCarrier Q hab hcd e z
    let w_H := -p
    let W := flatSourceQ3ActualWickRepresentative Q hab hcd e (m + 1) ω
    let u₁flat := flatFirstResponse hU hvol ν σ hν hσ k w_H
    let uFlat : pureFluxPair
        (Y := HilbertVectorL2 U)
        (X := (physicalPotentialSpace Q).toSubmodule) :=
      WithLp.toLp 2 (0, p)
    let V := physicalProjectedInsertion Q σ hσ H
    let C := pureFluxBlockOperator 0 V
    let sFlat : pureFluxPair
        (Y := HilbertVectorL2 U)
        (X := (physicalPotentialSpace Q).toSubmodule) :=
      WithLp.toLp 2 (-V w_H, 0)
    (u₁flat.down = Variational.hilbertPureSecondL2 U
        (p : HilbertVectorL2 U)) ∧
      (∀ n : Gaussian.whiteBasisIndex, ∀ i : Fin 2,
        (flatFirstResponseMode hU hvol ν σ hν hσ k β L n i).down =
          Variational.hilbertPureSecondL2 U (flatPureFluxMode Q β L n i)) ∧
      (C uFlat = sFlat) ∧
      sFlat = WithLp.toLp 2
        ((physicalFluxSpace Q).toSubmodule.subtypeL
          ((physicalFluxSpace Q).toSubmodule.orthogonalProjectionOnto
            (rotateVectorL2 Q W)),
          (0 : (physicalPotentialSpace Q).toSubmodule)) := by
  classical
  let U := openCubeSet Q
  let K := closedRectangle a₀ b₀ c₀ d₀
  have hQcl : closure U ⊆ K := by
    change closure (openCubeSet Q) ⊆ closedRectangle a₀ b₀ c₀ d₀
    rw [← rectangle_closure a₀ b₀ c₀ d₀ hab hcd]
    exact closure_mono hQ
  let hU := measurableSet_openCubeSet Q
  let hvol : 0 < (volume U).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  let ν := M.nu
  have hν : 0 < ν := M.nu_pos
  let σ : ℝ := Annealed.sigmaBar M m
  have hσ : 0 < σ := (Annealed.sigmaBar M m).property
  let β := q3ModelAmplitude M h (m + 1)
  let L := q3ModelLength (m + 1)
  let z := shellFieldScalarRestriction K (ω.1 (m + 1))
  let k := physicalResponseRestriction Q hQcl (olderField K m ω)
  let H := σ • physicalResponseRestriction Q hQcl z
  let p := flatSourcePotentialCarrier Q hab hcd e z
  let w_H := -p
  let W := flatSourceQ3ActualWickRepresentative Q hab hcd e (m + 1) ω
  let u₁flat := flatFirstResponse hU hvol ν σ hν hσ k w_H
  let uFlat : pureFluxPair (Y := HilbertVectorL2 U)
      (X := (physicalPotentialSpace Q).toSubmodule) :=
    WithLp.toLp 2 (0, p)
  let V := physicalProjectedInsertion Q σ hσ H
  let C := pureFluxBlockOperator 0 V
  let sFlat : pureFluxPair (Y := HilbertVectorL2 U)
      (X := (physicalPotentialSpace Q).toSubmodule) :=
    WithLp.toLp 2 (-V w_H, 0)
  change
    (u₁flat.down = Variational.hilbertPureSecondL2 U
        (p : HilbertVectorL2 U)) ∧
      (∀ n : Gaussian.whiteBasisIndex, ∀ i : Fin 2,
        (flatFirstResponseMode hU hvol ν σ hν hσ k β L n i).down =
          Variational.hilbertPureSecondL2 U (flatPureFluxMode Q β L n i)) ∧
      (C uFlat = sFlat) ∧
      sFlat = WithLp.toLp 2
        ((physicalFluxSpace Q).toSubmodule.subtypeL
          ((physicalFluxSpace Q).toSubmodule.orthogonalProjectionOnto
            (rotateVectorL2 Q W)),
          (0 : (physicalPotentialSpace Q).toSubmodule))
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [u₁flat, flatFirstResponse, w_H, U]
  · intro n i
    simp [flatFirstResponseMode, flatFirstResponse, U]
  · apply (WithLp.prodContinuousLinearEquiv 2 ℝ
      (HilbertVectorL2 U)
      ((physicalPotentialSpace Q).toSubmodule)).injective
    change (pureFluxBlockOperator 0 V uFlat).ofLp = (-V w_H, 0)
    rw [pureFluxBlockOperator_apply]
    simp [uFlat, w_H]
  · have hsource := flat_source_eq_flux_projection_of_rotated_wick
      Q hab hcd hQ hQcl σ hσ z e
    change WithLp.toLp 2 (-V w_H, 0) =
      WithLp.toLp 2
        ((physicalFluxSpace Q).toSubmodule.subtypeL
          ((physicalFluxSpace Q).toSubmodule.orthogonalProjectionOnto
            (rotateVectorL2 Q W)),
          (0 : (physicalPotentialSpace Q).toSubmodule))
    apply congrArg (fun y : HilbertVectorL2 (openCubeSet Q) =>
      WithLp.toLp 2
        (y, (0 : (physicalPotentialSpace Q).toSubmodule)))
    have hsign : -V w_H = V p := by simp [w_H, V]
    rw [hsign]
    simpa [V, H, W, z, K, σ, hσ,
      flatSourceQ3ActualWickRepresentative] using hsource

private theorem physical_positive_shear_scale_exchange
    (Q : TriadicCube 2) (σ : ℝ) (hσ : 0 < σ)
    (H : ResponseCoefficient (openCubeSet Q))
    (p : HilbertVectorL2 (openCubeSet Q)) :
    physicalPositiveShear Q σ hσ H (σ • p) =
      physicalPositiveShear Q σ hσ (σ • H) p := by
  change -(hilbertSecondProjection (openCubeSet Q)
      (responseShearL2Operator σ hσ H
        (hilbertPureFirstL2 (openCubeSet Q) (σ • p)))) =
    -(hilbertSecondProjection (openCubeSet Q)
      (responseShearL2Operator σ hσ (σ • H)
        (hilbertPureFirstL2 (openCubeSet Q) p)))
  have hfirst : hilbertPureFirstL2 (openCubeSet Q) (σ • p) =
      σ • hilbertPureFirstL2 (openCubeSet Q) p := map_smul _ σ p
  rw [hfirst, map_smul]
  rw [responseShearL2Operator_smul
    (measurableSet_openCubeSet Q) σ hσ σ H]
  rfl

/-- Transfer the flat source to the literal fresh coefficient used by the
physical parity quartic. The source potential carries the frame factor σ, so
the unprojected field is exactly the quarter-turn of the fixed Wick
representative; the physical flux projection remains explicit. -/
theorem actual_parity_flat_first_response_source_bridge
    (Q : TriadicCube 2) {a₀ b₀ c₀ d₀ : ℝ}
    (hab : a₀ < b₀) (hcd : c₀ < d₀)
    (hQ : openCubeSet Q ⊆ openRectangle a₀ b₀ c₀ d₀)
    (M : ABKModel 2) (h : ℝ) (m : ℤ)
    (ω : Cutoff.CutoffSample 2) (e : Vec 2) :
    let U := openCubeSet Q
    let K := closedRectangle a₀ b₀ c₀ d₀
    let hQcl : closure U ⊆ K := by
      change closure (openCubeSet Q) ⊆ closedRectangle a₀ b₀ c₀ d₀
      rw [← rectangle_closure a₀ b₀ c₀ d₀ hab hcd]
      exact closure_mono hQ
    let hU := measurableSet_openCubeSet Q
    let hvol : 0 < (volume U).toReal := by
      rw [volume_openCubeSet_toReal]
      exact cubeVolume_pos Q
    let ν := M.nu
    let hν : 0 < ν := M.nu_pos
    let σ : ℝ := Annealed.sigmaBar M m
    let hσ : 0 < σ := (Annealed.sigmaBar M m).property
    let β := q3ModelAmplitude M h (m + 1)
    let L := q3ModelLength (m + 1)
    let z := shellFieldScalarRestriction K (ω.1 (m + 1))
    let R := physicalResponseRestriction Q hQcl
    let k := R (olderField K m ω)
    let H := R z
    let p₀ := flatSourcePotentialCarrier Q hab hcd e z
    let p := σ • p₀
    let w_H := -p
    let W := flatSourceQ3ActualWickRepresentative Q hab hcd e (m + 1) ω
    let u₁flat := flatFirstResponse hU hvol ν σ hν hσ k w_H
    let uFlat : physicalParityHilbert Q := WithLp.toLp 2 (0, p)
    let V := physicalProjectedInsertion Q σ hσ H
    let C := pureFluxBlockOperator 0 V
    let sFlat : physicalParityHilbert Q := WithLp.toLp 2 (-V w_H, 0)
    (V = physicalParityCoefficient Q σ hσ R z) ∧
      (u₁flat.down = Variational.hilbertPureSecondL2 U
        (p : HilbertVectorL2 U)) ∧
      (∀ n : Gaussian.whiteBasisIndex, ∀ i : Fin 2,
        (σ • flatFirstResponseMode hU hvol ν σ hν hσ k β L n i).down =
          Variational.hilbertPureSecondL2 U
            (σ • flatPureFluxMode Q β L n i)) ∧
      (physicalPositiveShear Q σ hσ H (p : HilbertVectorL2 U) =
        rotateVectorL2 Q W) ∧
      (C uFlat = sFlat) ∧
      sFlat = WithLp.toLp 2
        ((physicalFluxSpace Q).toSubmodule.subtypeL
          ((physicalFluxSpace Q).toSubmodule.orthogonalProjectionOnto
            (rotateVectorL2 Q W)),
          (0 : (physicalPotentialSpace Q).toSubmodule)) := by
  classical
  let U := openCubeSet Q
  let K := closedRectangle a₀ b₀ c₀ d₀
  have hQcl : closure U ⊆ K := by
    change closure (openCubeSet Q) ⊆ closedRectangle a₀ b₀ c₀ d₀
    rw [← rectangle_closure a₀ b₀ c₀ d₀ hab hcd]
    exact closure_mono hQ
  let hU := measurableSet_openCubeSet Q
  have hvol : 0 < (volume U).toReal := by
    rw [volume_openCubeSet_toReal]
    exact cubeVolume_pos Q
  let ν := M.nu
  have hν : 0 < ν := M.nu_pos
  let σ : ℝ := Annealed.sigmaBar M m
  have hσ : 0 < σ := (Annealed.sigmaBar M m).property
  let β := q3ModelAmplitude M h (m + 1)
  let L := q3ModelLength (m + 1)
  let z := shellFieldScalarRestriction K (ω.1 (m + 1))
  let R := physicalResponseRestriction Q hQcl
  let k := R (olderField K m ω)
  let H := R z
  let p₀ := flatSourcePotentialCarrier Q hab hcd e z
  let p := σ • p₀
  let w_H := -p
  let W := flatSourceQ3ActualWickRepresentative Q hab hcd e (m + 1) ω
  let u₁flat := flatFirstResponse hU hvol ν σ hν hσ k w_H
  let uFlat : physicalParityHilbert Q := WithLp.toLp 2 (0, p)
  let V := physicalProjectedInsertion Q σ hσ H
  let C := pureFluxBlockOperator 0 V
  let sFlat : physicalParityHilbert Q := WithLp.toLp 2 (-V w_H, 0)
  change (V = physicalParityCoefficient Q σ hσ R z) ∧
      (u₁flat.down = Variational.hilbertPureSecondL2 U
        (p : HilbertVectorL2 U)) ∧
      (∀ n : Gaussian.whiteBasisIndex, ∀ i : Fin 2,
        (σ • flatFirstResponseMode hU hvol ν σ hν hσ k β L n i).down =
          Variational.hilbertPureSecondL2 U
            (σ • flatPureFluxMode Q β L n i)) ∧
      (physicalPositiveShear Q σ hσ H (p : HilbertVectorL2 U) =
        rotateVectorL2 Q W) ∧
      (C uFlat = sFlat) ∧
      sFlat = WithLp.toLp 2
        ((physicalFluxSpace Q).toSubmodule.subtypeL
          ((physicalFluxSpace Q).toSubmodule.orthogonalProjectionOnto
            (rotateVectorL2 Q W)),
          (0 : (physicalPotentialSpace Q).toSubmodule))
  have hraw : physicalPositiveShear Q σ hσ H
      (p : HilbertVectorL2 U) = rotateVectorL2 Q W := by
    have hscaled := flat_source_positive_shear_eq_rotated_wick
      Q hab hcd hQ hQcl σ hσ z e
    have hW : flatSourceQ3ShellProduct Q hab hcd e z = W := by
      simp [W, flatSourceQ3ActualWickRepresentative, z, K]
    calc
      physicalPositiveShear Q σ hσ H
          (p : HilbertVectorL2 U) =
          physicalPositiveShear Q σ hσ (σ • R z)
            (p₀ : HilbertVectorL2 U) := by
              simpa [H, p, p₀] using
                physical_positive_shear_scale_exchange Q σ hσ
                  (R z) (p₀ : HilbertVectorL2 U)
      _ = rotateVectorL2 Q
          (flatSourceQ3ShellProduct Q hab hcd e z) := hscaled
      _ = rotateVectorL2 Q W := congrArg (rotateVectorL2 Q) hW
  refine ⟨rfl, ?_, ?_, hraw, ?_, ?_⟩
  · simp [u₁flat, flatFirstResponse, w_H, p, U]
  · intro n i
    let D := responseFrameEnergyData hU hvol ν σ hν hσ k
    let f := flatPureFluxMode Q β L n i
    have hmode : flatFirstResponseMode hU hvol ν σ hν hσ k β L n i =
        responseEnergyUp D (Variational.hilbertPureSecondL2 U f) := by
      simp [flatFirstResponseMode, flatFirstResponse, D, f, U]
    rw [hmode]
    have hsmul : σ • responseEnergyUp D
        (Variational.hilbertPureSecondL2 U f) =
        responseEnergyUp D (σ • Variational.hilbertPureSecondL2 U f) := rfl
    rw [hsmul, responseEnergyUp_down, map_smul]
  · apply (WithLp.prodContinuousLinearEquiv 2 ℝ
      (HilbertVectorL2 U)
      ((physicalPotentialSpace Q).toSubmodule)).injective
    change (pureFluxBlockOperator 0 V uFlat).ofLp = (-V w_H, 0)
    rw [pureFluxBlockOperator_apply]
    simp [uFlat, w_H]
  · have hprojected := physical_insertion_eq_flux_projected_shear
      Q σ hσ H p
    change WithLp.toLp 2 (-V w_H, 0) =
      WithLp.toLp 2
        ((physicalFluxSpace Q).toSubmodule.subtypeL
          ((physicalFluxSpace Q).toSubmodule.orthogonalProjectionOnto
            (rotateVectorL2 Q W)),
          (0 : (physicalPotentialSpace Q).toSubmodule))
    apply congrArg (fun y : HilbertVectorL2 U =>
      WithLp.toLp 2 (y, (0 : (physicalPotentialSpace Q).toSubmodule)))
    have hsign : -V w_H = V p := by
      simp [w_H, V]
    rw [hsign]
    calc
      V p = physicalProjectedInsertion Q σ hσ H p := rfl
      _ = (physicalFluxSpace Q).toSubmodule.subtypeL
          ((physicalFluxSpace Q).toSubmodule.orthogonalProjectionOnto
            (physicalPositiveShear Q σ hσ H (p : HilbertVectorL2 U))) :=
        hprojected
      _ = (physicalFluxSpace Q).toSubmodule.subtypeL
          ((physicalFluxSpace Q).toSubmodule.orthogonalProjectionOnto
            (rotateVectorL2 Q W)) :=
        congrArg ((physicalFluxSpace Q).toSubmodule.subtypeL)
          (congrArg ((physicalFluxSpace Q).toSubmodule.orthogonalProjectionOnto)
            hraw)

/-- The actual fresh insertion retains its orthogonal projection onto the
physical flux space. -/
theorem actual_parity_flat_insertion_eq_flux_projection_of_wick
    (Q : TriadicCube 2) {a₀ b₀ c₀ d₀ : ℝ}
    (hab : a₀ < b₀) (hcd : c₀ < d₀)
    (hQ : openCubeSet Q ⊆ openRectangle a₀ b₀ c₀ d₀)
    (M : ABKModel 2) (h : ℝ) (m : ℤ)
    (ω : Cutoff.CutoffSample 2) (e : Vec 2) :
    let U := openCubeSet Q
    let K := closedRectangle a₀ b₀ c₀ d₀
    let hQcl : closure U ⊆ K := by
      change closure (openCubeSet Q) ⊆ closedRectangle a₀ b₀ c₀ d₀
      rw [← rectangle_closure a₀ b₀ c₀ d₀ hab hcd]
      exact closure_mono hQ
    let σ : ℝ := Annealed.sigmaBar M m
    let hσ : 0 < σ := (Annealed.sigmaBar M m).property
    let z := shellFieldScalarRestriction K (ω.1 (m + 1))
    let p₀ := flatSourcePotentialCarrier Q hab hcd e z
    let W := flatSourceQ3ActualWickRepresentative Q hab hcd e (m + 1) ω
    physicalProjectedInsertion Q σ hσ
      (physicalResponseRestriction Q hQcl z) (σ • p₀) =
      (physicalFluxSpace Q).toSubmodule.subtypeL
        ((physicalFluxSpace Q).toSubmodule.orthogonalProjectionOnto
          (rotateVectorL2 Q W)) := by
  let K := closedRectangle a₀ b₀ c₀ d₀
  let z := shellFieldScalarRestriction K (ω.1 (m + 1))
  let hQcl : closure (openCubeSet Q) ⊆ K := by
    change closure (openCubeSet Q) ⊆ closedRectangle a₀ b₀ c₀ d₀
    rw [← rectangle_closure a₀ b₀ c₀ d₀ hab hcd]
    exact closure_mono hQ
  let σ : ℝ := Annealed.sigmaBar M m
  have hσ : 0 < σ := (Annealed.sigmaBar M m).property
  let p₀ := flatSourcePotentialCarrier Q hab hcd e z
  let W := flatSourceQ3ActualWickRepresentative Q hab hcd e (m + 1) ω
  have hbridge := actual_parity_flat_first_response_source_bridge
    Q hab hcd hQ M h m ω e
  rcases hbridge with ⟨_, _, _, hraw, _, _⟩
  change physicalProjectedInsertion Q σ hσ
      (physicalResponseRestriction Q hQcl z) (σ • p₀) = _
  rw [physical_insertion_eq_flux_projected_shear]
  exact congrArg ((physicalFluxSpace Q).toSubmodule.subtypeL.comp
    ((physicalFluxSpace Q).toSubmodule.orthogonalProjectionOnto)) hraw

end ASDExplicitGamma.Scalar
