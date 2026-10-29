module

public import ASDExplicitGamma.Inverse.FullResponseActiveReferenceFrame
public import ASDExplicitGamma.Inverse.FullResponseDomainLoadPositivity
public import ASDExplicitGamma.Inverse.FullResponseActiveParentCharge

/-! The complete active normalized trace in the root reference frame, with actual parent wave means. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider Algsuperdiff.Section3.Provider.Whitney
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
open ASDExplicitGamma.Response ASDExplicitGamma.Variational
open scoped ENNReal

noncomputable section

/-- Exact observer clock times the source active trace coefficient on a parent. -/
def fullResponseReferenceParentCoefficient (M : ABKModel 2) (Q : TriadicCube 2)
    (H : ℕ) (J : ℤ) (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2)
    (P : WhitneyIndexedCell Q H) : ℝ :=
  rootAssemblyClock M.gamma H P.1 *
    (rootEdelta .full * (fullResponseTraceC0 +
      fullResponseTraceC1*(fullResponseParentWaveMean M P.2.val (Q.scale-342) J weights ω)^2))

theorem full_response_reference_parent_coefficient_nonneg
    (M : ABKModel 2) (Q : TriadicCube 2) (H : ℕ) (J : ℤ)
    (weights : ℤ → ℝ) (ω : Cutoff.CutoffSample 2) (P : WhitneyIndexedCell Q H) :
    0 ≤ fullResponseReferenceParentCoefficient M Q H J weights ω P := by
  dsimp only [fullResponseReferenceParentCoefficient, rootEdelta,
    fullResponseTraceC0, fullResponseTraceC1, rootTau, rootAssemblyClock]
  positivity

/-- The actual four-load active contribution, with its final normalization,
is paid by parent density integrals times the exact c₀ₜ/c₁ₜ wave coefficients.
Bad parents contribute zero through the actual stopped-gradient convention. -/
theorem full_response_active_reference_trace_le_parent_density_sum
    (M : ABKModel 2) (Q : TriadicCube 2) (H : ℕ)
    (hH : rootH0 .full ≤ H) (ω : Cutoff.CutoffSample 2)
    (hgood : ∀ k, H ≤ k → ω ∉ separationFailure
      (q3PlanarMarks M (Q.scale-k) (rootTau .full) (waveGateEta .full))
        k (rootBlockStart Q k))
    (J : ℤ) (hJ : Q.scale-1 ≤ J) (weights : ℤ → ℝ)
    (hw : ∀ k ∈ Finset.Ioc (Q.scale-342) J, 0 ≤ weights k ∧ weights k ≤ 1)
    (hfinite : ∀ j ≤ Q.scale-(H:ℤ), ∀ z,
      diameterField (q3PlanarMarks M j (rootTau .full) (waveGateEta .full)) ω z ≠ ∞)
    (C : HybridCell Q H (rootBadWhitneyCells M Q H (rootTau .full)
      (waveGateEta .full) ω) → Mat 2)
    (hCb : ∀ i, (hybridParent i).2.val ∈
      rootBadWhitneyCells M Q H (rootTau .full) (waveGateEta .full) ω → C i = 0)
    (hC : ∀ i, ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q),
      x ∈ (hybridDomain i : Set (Vec 2)) →
        stoppedKuhnGradient M Q H
          (by
            have hh : 333 ≤ rootH0 .full := by norm_num [rootH0]
            exact hh.trans hH)
          (rootTau .full) (waveGateEta .full) ω hgood
          (rootBadWhitneyCells M Q H (rootTau .full) (waveGateEta .full) ω)
          (fun V hV => hV.1) (fun V hV => hV.2) x = C i) :
    let S := rootBadWhitneyCells M Q H (rootTau .full) (waveGateEta .full) ω
    (∑ j : Fin 2 × Bool, ∑' i : HybridActiveCell Q H S, ENNReal.ofReal
      (((volume (hybridDomain (.inr i) : Set (Vec 2))).toReal /
        (volume (cubeSet Q)).toReal) *
          hybridFullTraceCellLoadEnergy (Annealed.sigmaBar M (Q.scale-1) : ℝ)
            (coarseBlockMatrix (hybridDomain (.inr i) : Set (Vec 2))
              (attenuatedCoefficient M (Q.scale-342) J weights ω)) (C (.inr i)) j)) *
                ENNReal.ofReal (1/4:ℝ) ≤
      ∑' P : WhitneyIndexedCell Q H, ENNReal.ofReal
        (fullResponseReferenceParentCoefficient M Q H J weights ω P *
          (planarGradientCharge 40+1) *
            (∑ e : Fin 3, ∫ x in cubeSet P.2.val,
              (layerResolutionDiameter M Q H (rootTau .full) (waveGateEta .full)
                P.1 e ω x)^2)/(volume (cubeSet Q)).toReal) := by
  classical
  dsimp only
  let S := rootBadWhitneyCells M Q H (rootTau .full) (waveGateEta .full) ω
  let b := fullResponseReferenceParentCoefficient M Q H J weights ω
  let w (i : HybridActiveCell Q H S) :=
    (volume (hybridDomain (.inr i) : Set (Vec 2))).toReal/(volume (cubeSet Q)).toReal
  let load (i : HybridActiveCell Q H S) (j : Fin 2 × Bool) :=
    hybridFullTraceCellLoadEnergy (Annealed.sigmaBar M (Q.scale-1) : ℝ)
      (coarseBlockMatrix (hybridDomain (.inr i) : Set (Vec 2))
        (attenuatedCoefficient M (Q.scale-342) J weights ω)) (C (.inr i)) j
  have h333 : 333 ≤ H := by norm_num [rootH0] at hH; omega
  have hw0 (i : HybridActiveCell Q H S) : 0 ≤ w i :=
    div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hb (P : WhitneyIndexedCell Q H) : 0 ≤ b P :=
    full_response_reference_parent_coefficient_nonneg M Q H J weights ω P
  have hcharge := hybrid_active_gradient_square_sum_le_parent_densities
    M Q H h333 (rootTau .full) (waveGateEta .full) ω hgood S
    (fun V hV => hV.1) (fun V hV => hV.2) hfinite C hC b hb
  have hterm (i : HybridActiveCell Q H S) :
      (∑ j : Fin 2 × Bool, ENNReal.ofReal (w i*load i j)) * ENNReal.ofReal (1/4:ℝ) ≤
        ENNReal.ofReal (b (hybridParent (.inr i))*
          (volume (hybridDomain (.inr i) : Set (Vec 2))).toReal /
            (volume (cubeSet Q)).toReal *
              ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (C (.inr i))‖^2) := by
    by_cases hbad : (hybridParent (.inr i)).2.val ∈ S
    · have hzero := hCb (.inr i) hbad
      simp [load, hzero, planar_flux_matrix_zero, hybridFullTraceCellLoadEnergy,
        blockVecDot, blockMatVecMul, vecDot, matVecMul]
    · let G := rootAssemblyClock M.gamma H (hybridParent (.inr i)).1
      let F := 4*‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) (C (.inr i))‖^2
      let cap := rootEdelta .full*(fullResponseTraceC0 +
        fullResponseTraceC1*(fullResponseParentWaveMean M
          (hybridParent (.inr i)).2.val (Q.scale-342) J weights ω)^2)
      have hG : 0 ≤ G := by dsimp only [G, rootAssemblyClock]; positivity
      have hF : 0 ≤ F := by dsimp only [F]; positivity
      have hlocal := full_response_active_reference_trace_root_mean_le
        M Q H hH ω J hJ weights hw C i hbad
      have hlocal' : ENNReal.ofReal (∑ j, load i j) ≤
          ENNReal.ofReal (G*(F*cap)) := by
        rw [ENNReal.ofReal_mul hG, ENNReal.ofReal_mul hF]
        exact hlocal
      have hscaled := mul_le_mul_of_nonneg_left hlocal'
        (show 0 ≤ ENNReal.ofReal (w i/4) from bot_le)
      rw [← ENNReal.ofReal_mul (div_nonneg (hw0 i) (by norm_num)),
        ← ENNReal.ofReal_mul (div_nonneg (hw0 i) (by norm_num))] at hscaled
      have hload0 (j : Fin 2 × Bool) : 0 ≤ load i j :=
        attenuated_domain_full_trace_cell_load_nonneg M Q (hybridDomain (.inr i))
          (hybrid_domain_subset_root (.inr i)) (Q.scale-342) J (by omega)
          weights ω (Annealed.sigmaBar M (Q.scale-1) : ℝ) (C (.inr i)) j
      have hsum : (∑ j : Fin 2 × Bool, ENNReal.ofReal (w i*load i j)) *
          ENNReal.ofReal (1/4:ℝ) = ENNReal.ofReal ((w i/4)*∑ j, load i j) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => mul_nonneg (hw0 i) (hload0 j)),
          ← Finset.mul_sum]
        rw [mul_comm _ (ENNReal.ofReal (1/4:ℝ)),
          ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/4)]
        congr 1
        ring
      rw [hsum]
      apply hscaled.trans_eq
      congr 1
      dsimp only [G, F, cap, b, fullResponseReferenceParentCoefficient, w]
      ring
  calc
    _ = (∑' i : HybridActiveCell Q H S,
        ∑ j : Fin 2 × Bool, ENNReal.ofReal (w i*load i j))*ENNReal.ofReal (1/4:ℝ) := by
      congr 1
      simpa only [tsum_fintype] using
        (ENNReal.tsum_comm (f := fun j i => ENNReal.ofReal (w i*load i j)))
    _ = ∑' i : HybridActiveCell Q H S,
        (∑ j : Fin 2 × Bool, ENNReal.ofReal (w i*load i j))*ENNReal.ofReal (1/4:ℝ) := by
      rw [ENNReal.tsum_mul_right]
    _ ≤ _ := (ENNReal.tsum_le_tsum hterm).trans hcharge

end
end ASDExplicitGamma.Inverse
