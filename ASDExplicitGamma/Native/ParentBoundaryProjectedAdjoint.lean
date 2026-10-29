module

public import ASDExplicitGamma.Main.InverseLowerCenteredRowBound
public import ASDExplicitGamma.Main.InverseLowerProjection
public import ASDExplicitGamma.Native.ParentBoundaryVariationWeak

/-! Sharp inverse-history coercivity in the actual centered projected-adjoint covariance row. -/

@[expose] public section

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse
  ASDExplicitGamma.Response ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open scoped BigOperators

namespace ASDExplicitGamma.Native
open ASDExplicitGamma.Main

/-- The centered source row controls the direct sum of projected-adjoint
sources at every aligned source depth. -/
theorem parent_boundary_centered_projected_adjoint_row
    (n : ℤ) (q i m : ℕ) (ν σ b : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (L : {l : ℝ // 0 < l}) (s : Finset whiteBasisIndex)
    (hρ : cubeScaleFactor (originCube 2 n)/L.1 = pureFluxCovarianceRho q i)
    (hδ : diagMeshRadius (originCube 2 n) m/L.1 = pureFluxCovarianceDelta q i)
    (k : ResponseCoefficient (openCubeSet (originCube 2 n))) (B : ℝ) (hB : 0≤B)
    (hhist : ∀ U∈descendantsAtDepth (originCube 2 n) m,
      lemmaVInverseHistory U (responseFramePlanarCoefficientField ν σ k) ((3:ℝ)^(1/4:ℝ))≤B)
    (P : BlockVec 2)
    (u : AHarmonicFunction (responseFramePlanarCoefficientField ν σ k)
      (openCubeSet (originCube 2 n)))
    (w : AHarmonicFunction
      (adjointCoeffField (responseFramePlanarCoefficientField ν σ k))
      (openCubeSet (originCube 2 n)))
    (hrep : hilbertBlockL2ToBlockL2
        ((responseFrameMuOperatorSystemData
          (isOpenBoundedConvexDomain_openCubeSet (originCube 2 n)).isOpen.measurableSet
          (volume_openCubeSet_originCube_toReal_pos (d := 2) n)
          ν σ hν hσ k).toMuHilbertRealization.minimizerMap P) =ᵐ[
          volumeMeasureOn (openCubeSet (originCube 2 n))]
        (fun x => (blockResponsePairHalfState
          (responseFramePlanarCoefficientField ν σ k) u w).eval x)) :
    let Q := originCube 2 n
    let M := responseFrameMuOperatorSystemData
      (measurableSet_openCubeSet Q)
      (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ k
    let D := responseEnergyHilbertData M.toMuHilbertRealization
    let V := responseEnergyCorrectionSpace M.toMuHilbertRealization D
    let S := responseFrameEnergyBaseMinimizer
      (measurableSet_openCubeSet Q)
      (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ k P
    let C := responseFrameEnergyShearFamily
      (measurableSet_openCubeSet Q)
      (volume_openCubeSet_originCube_toReal_pos (d := 2) n) ν σ hν hσ k
    let H (l : whiteBasisIndex) := pureFluxMainCubeQ3CenteredResponseCoefficient n b L
      (@Encodable.encode whiteBasisIndex
        (Encodable.ofCountable whiteBasisIndex) l)
    let g : H1Function (openCubeSet Q) := (1 / 2 : ℝ) • (w.toH1-u.toH1)
    (∑ l : {l : whiteBasisIndex // l ∈ s},
      ‖(V.toSubmodule.orthogonalProjectionOnto
        ((C (H l.1)).adjoint S) : EnergyCarrier D)‖ ^ 2) ≤
      (|σ⁻¹| * |b| * pureFluxCovarianceB q i * Real.sqrt B *
        Real.sqrt (lemmaVTiledWeakEnergy Q m g.grad)) ^ 2 := by
  classical
  intro Q M D V S C H g
  let I := {l : whiteBasisIndex // l ∈ s}
  let E := EnergyCarrier D
  let Op : I → E →L[ℝ] E := fun i => C (H i.1)
  let κ := |σ⁻¹| * |b| * pureFluxCovarianceB q i *
    Real.sqrt B * Real.sqrt (lemmaVTiledWeakEnergy Q m g.grad)
  have hκ : 0 ≤ κ := by
    dsimp [κ]
    exact mul_nonneg (mul_nonneg
      (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        (pureFlux_covariance_rows_order q i).1)
      (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hrow : ∀ T : I → V.toSubmodule,
      |∑ i : I, inner ℝ S (Op i (T i : E))| ≤
        κ * Real.sqrt (∑ i : I, ‖(T i : E)‖ ^ 2) := by
    intro T
    let Y : whiteBasisIndex → V.toSubmodule := fun l =>
      if hl : l ∈ s then T ⟨l, hl⟩ else 0
    obtain ⟨p, hpFirst, _hpEnergy, hpPair⟩ :=
      main_q3_centered_variation_family_shear_pairing_bound
        n q i m ν σ b hν hσ L s hρ hδ k P u w hrep Y
    have hweakSubtype :
        (∑ i : I, lemmaVTiledWeakEnergy Q m (p i.1).toH1Function.grad) =
          ∑ l ∈ s, lemmaVTiledWeakEnergy Q m (p l).toH1Function.grad := by
      exact (Finset.sum_subtype s (fun _ => Iff.rfl)
        (fun l : whiteBasisIndex =>
          lemmaVTiledWeakEnergy Q m (p l).toH1Function.grad)).symm
    have hweakSum :
        (∑ l ∈ s, lemmaVTiledWeakEnergy Q m (p l).toH1Function.grad) ≤
          B * ∑ i : I, ‖(T i : E)‖ ^ 2 := by
      rw [← hweakSubtype]
      calc
        _ ≤ ∑ i : I, B * ‖(T i : E)‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro i hi
          have hY : (Y i.1 : E) = (T i : E) := by
            simp [Y, i.2]
          rw [← hY]
          exact parent_boundary_variation_tiled_weak n ν σ hν hσ k
            (Y i.1) (p i.1) (hpFirst i.1) m B hhist
        _ = _ := by rw [← Finset.mul_sum]
    have hsqrt :
        Real.sqrt (∑ l ∈ s, lemmaVTiledWeakEnergy Q m (p l).toH1Function.grad) ≤
          Real.sqrt B * Real.sqrt (∑ i : I, ‖(T i : E)‖ ^ 2) := by
      calc
        _ ≤ Real.sqrt (B * ∑ i : I, ‖(T i : E)‖ ^ 2) :=
          Real.sqrt_le_sqrt hweakSum
        _ = _ := by rw [Real.sqrt_mul hB]
    have hsum :
        (∑ i : I, inner ℝ S (Op i (T i : E))) =
          ∑ l ∈ s, inner ℝ S (C (H l) (Y l : E)) := by
      have hsub :
          (∑ l ∈ s, inner ℝ S (C (H l) (Y l : E))) =
            ∑ i : I, inner ℝ S (C (H i.1) (Y i.1 : E)) :=
        Finset.sum_subtype s (fun _ => Iff.rfl) _
      calc
        _ = ∑ i : I, inner ℝ S (C (H i.1) (Y i.1 : E)) := by
          apply Finset.sum_congr rfl
          intro i hi
          simp [Op, Y, i.property]
        _ = _ := hsub.symm
    have hpair :
        |∑ i : I, inner ℝ S (Op i (T i : E))| ≤
          |σ⁻¹| * |b| * pureFluxCovarianceB q i *
            Real.sqrt (∑ l ∈ s,
              lemmaVTiledWeakEnergy Q m (p l).toH1Function.grad) *
            Real.sqrt (lemmaVTiledWeakEnergy Q m g.grad) := by
      rw [hsum]
      simpa [Q, D, S, C, H, g] using hpPair
    have hcoef : 0 ≤ |σ⁻¹| * |b| * pureFluxCovarianceB q i :=
      mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        (pureFlux_covariance_rows_order q i).1
    calc
      _ ≤ (|σ⁻¹| * |b| * pureFluxCovarianceB q i) *
          Real.sqrt (∑ l ∈ s,
            lemmaVTiledWeakEnergy Q m (p l).toH1Function.grad) *
          Real.sqrt (lemmaVTiledWeakEnergy Q m g.grad) := by
        exact hpair
      _ ≤ ((|σ⁻¹| * |b| * pureFluxCovarianceB q i) *
          (Real.sqrt B * Real.sqrt (∑ i : I, ‖(T i : E)‖ ^ 2))) *
          Real.sqrt (lemmaVTiledWeakEnergy Q m g.grad) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsqrt hcoef) (Real.sqrt_nonneg _)
      _ = κ * Real.sqrt (∑ i : I, ‖(T i : E)‖ ^ 2) := by
        dsimp [κ]
        ring
  have hproj := main_projected_adjoint_row_norm_sq_le V Op S κ hκ hrow
  simpa only [I, E, Op, κ, Submodule.coe_orthogonalProjectionOnto_apply] using hproj

end ASDExplicitGamma.Native

end
