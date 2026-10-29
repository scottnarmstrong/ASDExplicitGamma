module

public import ASDExplicitGamma.Main.InverseLowerCenteredProjectedQ3
public import ASDExplicitGamma.Inverse.PureFluxGeneratorSource

/-! The centered projected-adjoint sources have a summable covariance trace. -/

@[expose] public section

open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Inverse
  ASDExplicitGamma.Response ASDExplicitGamma.Triadic ASDExplicitGamma.Variational
open scoped BigOperators

namespace ASDExplicitGamma.Main

/-- The actual centered q3 projected-adjoint sources are square summable over
the covariance basis, with the exact source-row coefficient. -/
theorem main_q3_centered_projected_adjoint_source_trace_bound
    (n : ℤ) (q i m : ℕ) (ν σ b : ℝ) (hν : 0 < ν) (hσ : 0 < σ)
    (L : {l : ℝ // 0 < l})
    (hρ : cubeScaleFactor (originCube 2 n)/L.1 = pureFluxCovarianceRho q i)
    (hδ : diagMeshRadius (originCube 2 n) m/L.1 = pureFluxCovarianceDelta q i)
    (k : ResponseCoefficient (openCubeSet (originCube 2 n))) (P : BlockVec 2)
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
    let H (l : whiteBasisIndex) := pureFluxMainCubeQ3CenteredResponseCoefficient n b L
      (@Encodable.encode whiteBasisIndex
        (Encodable.ofCountable whiteBasisIndex) l)
    let g : H1Function (openCubeSet Q) := (1 / 2 : ℝ) • (w.toH1-u.toH1)
    let Z (l : whiteBasisIndex) := pureFluxResponseGeneratorZ
      (measurableSet_openCubeSet Q)
      (volume_openCubeSet_originCube_toReal_pos (d := 2) n)
      ν σ hν hσ P k (H l)
    let κ := |σ⁻¹| * |b| * pureFluxCovarianceB q i *
      Real.sqrt (σ / ν) * Real.sqrt (lemmaVTiledWeakEnergy Q m g.grad)
    Summable (fun l => ‖Z l‖^2) ∧ (∑' l, ‖Z l‖^2) ≤ κ^2 := by
  classical
  let Q := originCube 2 n
  let hv := volume_openCubeSet_originCube_toReal_pos (d := 2) n
  let hU := measurableSet_openCubeSet Q
  let M := responseFrameMuOperatorSystemData hU hv ν σ hν hσ k
  let D := responseEnergyHilbertData M.toMuHilbertRealization
  let V := responseEnergyCorrectionSpace M.toMuHilbertRealization D
  let S := responseFrameEnergyBaseMinimizer hU hv ν σ hν hσ k P
  let C := responseFrameEnergyShearFamily hU hv ν σ hν hσ k
  let H (l : whiteBasisIndex) := pureFluxMainCubeQ3CenteredResponseCoefficient n b L
    (@Encodable.encode whiteBasisIndex
      (Encodable.ofCountable whiteBasisIndex) l)
  let g : H1Function (openCubeSet Q) := (1 / 2 : ℝ) • (w.toH1-u.toH1)
  let Z (l : whiteBasisIndex) :=
    pureFluxResponseGeneratorZ hU hv ν σ hν hσ P k (H l)
  let κ := |σ⁻¹| * |b| * pureFluxCovarianceB q i *
    Real.sqrt (σ / ν) * Real.sqrt (lemmaVTiledWeakEnergy Q m g.grad)
  have hκ : 0 ≤ κ := by
    dsimp [κ]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
          (pureFlux_covariance_rows_order q i).1)
        (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)
  have hZeq (l : whiteBasisIndex) :
      ‖Z l‖^2 = ‖(V.toSubmodule.orthogonalProjectionOnto
        ((C (H l)).adjoint S) : EnergyCarrier D)‖^2 := by
    rfl
  have hfinite (s : Finset whiteBasisIndex) :
      (∑ l ∈ s, ‖Z l‖^2) ≤ κ^2 := by
    have hproj := main_q3_centered_projected_adjoint_row_norm_sq_le
      n q i m ν σ b hν hσ L s hρ hδ k P u w hrep
    have hsum : (∑ l ∈ s, ‖Z l‖^2) =
        ∑ l : {l : whiteBasisIndex // l ∈ s},
          ‖(V.toSubmodule.orthogonalProjectionOnto
            ((C (H l.1)).adjoint S) : EnergyCarrier D)‖^2 := by
      calc
        _ = ∑ l : {l : whiteBasisIndex // l ∈ s}, ‖Z l.1‖^2 :=
          Finset.sum_subtype s (fun _ => Iff.rfl) (fun l => ‖Z l‖^2)
        _ = _ := Finset.sum_congr rfl fun l _ => hZeq l.1
    dsimp only [Q, M, D, V, S, C, H, g, κ,
      Submodule.coe_orthogonalProjectionOnto_apply] at hproj ⊢
    rw [hsum]
    exact hproj
  have hZnonneg (l : whiteBasisIndex) : 0 ≤ ‖Z l‖^2 := sq_nonneg _
  have hsum : Summable (fun l => ‖Z l‖^2) :=
    summable_of_sum_le hZnonneg hfinite
  refine ⟨hsum, ?_⟩
  exact Real.tsum_le_of_sum_le hZnonneg hfinite

end ASDExplicitGamma.Main

end
