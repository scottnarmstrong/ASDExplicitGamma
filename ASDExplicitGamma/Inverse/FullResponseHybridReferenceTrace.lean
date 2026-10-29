module

public import ASDExplicitGamma.Inverse.OrderBandBounds
public import ASDExplicitGamma.Inverse.HybridFullTraceComparison
public import ASDExplicitGamma.Inverse.GoodCellResponse
public import ASDExplicitGamma.Inverse.FullResponseTrace

/-! Full-response four-load hybrid comparison in an arbitrary true reference frame. -/

@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Response ASDExplicitGamma.Variational ASDExplicitGamma.Triadic
open scoped ENNReal
noncomputable section

/-- At any successful selected height, the full normalized trace is bounded
by the actual identity-cell and active-simplex load sums. The same stopped
Kuhn map serves all four loads, and the exact factor `1/4` is retained. -/
theorem full_response_actual_trace_le_hybrid
    (M : ABKModel 2) (Q : TriadicCube 2) (H : ℕ)
    (hH : 377 ≤ H) (ω : Cutoff.CutoffSample 2)
    (hgood : ∀ k, H ≤ k → ω ∉ separationFailure
      (q3PlanarMarks M (Q.scale-k) (rootTau .full)
        (ASDExplicitGamma.Gaussian.waveGateEta .full)) k (rootBlockStart Q k))
    (m J ref : ℤ) (hm : m ≤ J) (weights : ℤ → ℝ) :
    let S := rootBadWhitneyCells M Q H (rootTau .full)
      (ASDExplicitGamma.Gaussian.waveGateEta .full) ω
    ∃ C : HybridCell Q H S → Mat 2,
      (∀ i : HybridIdentityCell Q H S, C (.inl i)=1) ∧
      (∀ i, (hybridParent i).2.val ∈ S → C i=0) ∧
      (∀ i, ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q),
        x ∈ (hybridDomain i : Set (Vec 2)) →
          stoppedKuhnGradient M Q H
            (by
              omega)
            (rootTau .full) (ASDExplicitGamma.Gaussian.waveGateEta .full)
            ω hgood S (fun V hV => hV.1) (fun V hV => hV.2) x = C i) ∧
      ENNReal.ofReal (rootTraceObservable M Q m J ref weights ω/4) ≤
        (∑ j : Fin 2 × Bool, ∑' i : HybridCell Q H S, ENNReal.ofReal
          (((volume (hybridDomain i : Set (Vec 2))).toReal /
              (volume (cubeSet Q)).toReal) *
            hybridFullTraceCellLoadEnergy (Annealed.sigmaBar M ref : ℝ)
              (coarseBlockMatrix (hybridDomain i : Set (Vec 2))
                (attenuatedCoefficient M m J weights ω)) (C i) j)) *
          ENNReal.ofReal (1/4:ℝ) := by
  classical
  dsimp only
  let S := rootBadWhitneyCells M Q H (rootTau .full)
    (ASDExplicitGamma.Gaussian.waveGateEta .full) ω
  let σ := (Annealed.sigmaBar M ref : ℝ)
  let A := coarseBlockMatrix (cubeSet Q) (attenuatedCoefficient M m J weights ω)
  have hσ : 0 < σ := (Annealed.sigmaBar_characterization M ref).1
  obtain ⟨C,hCi,hCb,hCa,hcmp⟩ :=
    actual_hybrid_full_trace_load_sum_comparison M Q H .full
      (by simpa only [rootH0] using hH) (rootTau .full)
      (ASDExplicitGamma.Gaussian.waveGateEta .full) ω hgood m J hm weights σ hσ
  let load : Fin 2 × Bool → ℝ := fun j => hybridFullTraceLoadEnergy σ A j
  have hbook : Book.Ch02.coarseBlockMatrix (Book.Ch02.cubeDomain Q)
      (sensitivityBookCoeffOn Q M.nu M.nu_pos
        (oldResponseCoefficient Q m ω +
          laterResponseCoefficient Q m J (sourceBandWeights m weights) ω)) = A := by
    exact attenuated_sensitivity_matrix_eq M Q m m J le_rfl hm weights ω
  have hquad (P : BlockVec 2) :
      0 ≤ blockVecDot P (blockMatVecMul A P) := by
    by_cases hP : P = 0
    · rw [hP]
      simp [blockVecDot, blockMatVecMul, vecDot, matVecMul]
    · rw [← hbook]
      exact (Book.Ch02.blockCoarseMatrixTheory (Book.Ch02.cubeDomain Q)
        (sensitivityBookCoeffOn Q M.nu M.nu_pos
          (oldResponseCoefficient Q m ω +
            laterResponseCoefficient Q m J (sourceBandWeights m weights) ω))).block_matrix_posDef
              P hP |>.le
  have hload0 (j : Fin 2 × Bool) : 0 ≤ load j := by
    dsimp only [load, hybridFullTraceLoadEnergy]
    exact hquad _
  have htrace :
      rootTraceObservable M Q m J ref weights ω/4 =
        (∑ j : Fin 2 × Bool, load j) / 4 := by
    change Matrix.trace (toFullBlockMat (frameMatrix (Annealed.sigmaBar M ref : ℝ)
      (coarseBlockMatrix (cubeSet Q) (attenuatedCoefficient M m J weights ω)))) / 4 = _
    rw [full_response_frame_trace_eq_scaled_loads _ _ (by simpa [σ] using hσ)]
    simp [load, σ, A, hybridFullTraceLoadEnergy]
  have hroot :
      ENNReal.ofReal (rootTraceObservable M Q m J ref weights ω/4) =
        ENNReal.ofReal (1/4:ℝ) *
          (∑ j : Fin 2 × Bool, ENNReal.ofReal (load j)) := by
    rw [htrace]
    have hquarter : 0 ≤ (1/4:ℝ) := by norm_num
    calc
      _ = ENNReal.ofReal ((1/4:ℝ) * ∑ j : Fin 2 × Bool, load j) := by
        congr 1
        ring
      _ = ENNReal.ofReal (1/4:ℝ) * ENNReal.ofReal (∑ j : Fin 2 × Bool, load j) :=
        ENNReal.ofReal_mul hquarter
      _ = ENNReal.ofReal (1/4:ℝ) *
          (∑ j : Fin 2 × Bool, ENNReal.ofReal (load j)) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => hload0 j)]
      _ = _ := rfl
  have hmul := mul_le_mul_right hcmp (ENNReal.ofReal (1/4:ℝ))
  rw [← hroot] at hmul
  refine ⟨C,hCi,hCb,hCa,?_⟩
  calc
    _ ≤ ENNReal.ofReal (1/4:ℝ) *
        (∑ j : Fin 2 × Bool, ∑' i : HybridCell Q H S, ENNReal.ofReal
          (((volume (hybridDomain i : Set (Vec 2))).toReal /
              (volume (openCubeSet Q)).toReal) *
            hybridFullTraceCellLoadEnergy σ
              (coarseBlockMatrix (hybridDomain i : Set (Vec 2))
                (attenuatedCoefficient M m J weights ω)) (C i) j)) := by
      simpa only [S, σ, volume_openCubeSet_toReal, volume_cubeSet_toReal] using hmul
    _ = (∑ j : Fin 2 × Bool, ∑' i : HybridCell Q H S, ENNReal.ofReal
          (((volume (hybridDomain i : Set (Vec 2))).toReal /
              (volume (openCubeSet Q)).toReal) *
            hybridFullTraceCellLoadEnergy σ
              (coarseBlockMatrix (hybridDomain i : Set (Vec 2))
                (attenuatedCoefficient M m J weights ω)) (C i) j)) *
          ENNReal.ofReal (1/4:ℝ) := by rw [mul_comm]
    _ = _ := by
      congr 1
      simp only [S, σ, volume_openCubeSet_toReal, volume_cubeSet_toReal]

end
end ASDExplicitGamma.Inverse
