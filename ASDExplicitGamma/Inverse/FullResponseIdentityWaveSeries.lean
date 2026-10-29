module

public import ASDExplicitGamma.Inverse.FullResponseIdentitySelectedWave
public import ASDExplicitGamma.Inverse.FullResponseIdentityWaveReconstruction
public import ASDExplicitGamma.Inverse.FullResponseWaveLayerProfile

/-! The complete selected identity shear-wave series with its exact v_k weights. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Model ASDExplicitGamma.Gaussian
open scoped ENNReal
noncomputable section

/-- Nonnegative scalar multiplication and the Lp triangle inequality, keeping
both scalar coefficients exact. -/
theorem full_response_linear_family_Lp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p : ℝ≥0∞) (hp : 1 ≤ p) (f g : Ω → ℝ)
    (a b F G : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hf : eLpNorm f p μ ≤ ENNReal.ofReal F)
    (hg : eLpNorm g p μ ≤ ENNReal.ofReal G) :
    eLpNorm (fun ω => a*f ω+b*g ω) p μ ≤ ENNReal.ofReal (a*F+b*G) := by
  have he : (fun ω => a*f ω+b*g ω) = a • f+b • g := rfl
  rw [he]
  apply (eLpNorm_add_le hp).trans
  rw [eLpNorm_const_smul,eLpNorm_const_smul,Real.enorm_eq_ofReal ha,Real.enorm_eq_ofReal hb]
  apply (add_le_add (mul_le_mul_of_nonneg_left hf bot_le)
    (mul_le_mul_of_nonneg_left hg bot_le)).trans_eq
  rw [← ENNReal.ofReal_mul ha,← ENNReal.ofReal_mul hb,
    ← ENNReal.ofReal_add (mul_nonneg ha hF) (mul_nonneg hb hG)]

/-- Measurability of a countably selected measurable family. -/
theorem full_response_selected_family_measurable {Ω : Type*} [MeasurableSpace Ω]
    (H : Ω → ℕ) (hH : Measurable H) (f : ℕ → Ω → ℝ)
    (hf : ∀ n, Measurable (f n)) : Measurable (fun ω => f (H ω) ω) := by
  have hh : Measurable (fun z : Ω × ℕ => f z.2 z.1) :=
    measurable_from_prod_countable_left hf
  exact hh.comp (measurable_id.prodMk hH)

/-- Actual clocked identity half mean-square on one selected Whitney layer. -/
def fullResponseIdentityWaveTerm (M : ABKModel 2) (Q : TriadicCube 2)
    (N : ℤ) (weights : ℤ → ℝ) (k : ℕ) (ω : Cutoff.CutoffSample 2) : ℝ :=
  let H := rootSelectedHeight M Q .full ω
  let x := (localizationResetAbscissa (377-38) (H-377) k:ℝ)
  (3:ℝ)^(2*M.gamma*x)*
    (assemblyLayerMeanSquare M Q H (k+1) N
      (sourceBandWeights (Q.scale-342) weights) ω/2)

/-- Its deterministic norm envelope is the literal identity W₀/W₁ layer payment. -/
def fullResponseIdentityWaveTermBudget (γ p D : ℝ) (k : ℕ) : ℝ :=
  (γ*(3:ℝ)^(2*γ*D)/4)*bankLayerWeight k*(3:ℝ)^(4*γ*(localizationProfileDepth (k+1):ℝ))*
    ((D+(localizationProfileDepth (k+1):ℝ))*physicalSelectedWaveBudget γ p 377 0+
      physicalSelectedWaveBudget γ p 377 1)

/-- The source W_j profiles are nonnegative. -/
theorem full_response_selected_wave_budget_nonneg (γ p : ℝ) (hp : 0 ≤ p) (j : Fin 2) :
    0 ≤ physicalSelectedWaveBudget γ p 377 j := by
  unfold physicalSelectedWaveBudget physicalSelectedWaveFiniteBudget selectedWaveTailBudget
  unfold selectedFirstClock selectedTailProbability
  positivity

/-- Each actual selected identity layer has the exact source scalar payment. -/
theorem full_response_identity_wave_term_Lp
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (Q : TriadicCube 2)
    (hpast : ∀ n ≤ Q.scale-337, nativeInductionState M h n)
    (N : ℤ) (hN : Q.scale-1 ≤ N) (weights : ℤ → ℝ)
    (hw : ∀ j ∈ Finset.Ioc (Q.scale-342) N, 0 ≤ weights j ∧ weights j ≤ 1)
    (k : ℕ) (p : ℝ) (hp : 2 ≤ p) (hp256 : p ≤ 256) :
    Measurable (fullResponseIdentityWaveTerm M Q N weights k) ∧
      eLpNorm (fullResponseIdentityWaveTerm M Q N weights k) (ENNReal.ofReal p)
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal
          (fullResponseIdentityWaveTermBudget M.gamma p ((N:ℝ)-(Q.scale:ℝ)+1) k) := by
  let H := rootSelectedHeight M Q .full
  let D := (N:ℝ)-(Q.scale:ℝ)+1
  let f := (localizationProfileDepth (k+1):ℝ)
  let C := (M.gamma*(3:ℝ)^(2*M.gamma*D)/4)*bankLayerWeight k*(3:ℝ)^(4*M.gamma*f)
  let W := fun j : Fin 2 => fun ω => fullResponseIdentityWeightedWave M Q N weights k j (H ω) ω
  have hH : Measurable H := q3_stopped_height_measurable M Q 377 (rootTau .full)
    (waveGateEta (rootWaveTuple .full))
  have hprotected : ∀ n ≤ Q.scale-342, nativeInductionState M h n := by
    intro n hn
    apply hpast n
    omega
  have hm (j : Fin 2) : Measurable (W j) := by
    exact full_response_selected_family_measurable H hH
      (fullResponseIdentityWeightedWave M Q N weights k j)
      (full_response_identity_weighted_wave_measurable M h hM Q hprotected N hN weights hw k j)
  have hb (j : Fin 2) := full_response_identity_selected_wave_Lp M h hM hg Q hpast
    N hN weights hw k j p hp hp256
  have hD : 0 ≤ D := by dsimp only [D]; exact_mod_cast (show 0 ≤ N-Q.scale+1 by omega)
  have hDf : 0 ≤ D+f := add_nonneg hD (Nat.cast_nonneg _)
  have hC : 0 ≤ C := by
    have hγ := M.shellPrefix.gamma_pos.le
    have hv := bankLayerWeight_nonneg k
    dsimp only [C]
    positivity
  have he : fullResponseIdentityWaveTerm M Q N weights k =
      fun ω => (C*(D+f))*W 0 ω+C*W 1 ω := by
    funext ω
    have hge : 377 ≤ H ω := q3_stopped_height_ge M Q 377 (rootTau .full)
      (waveGateEta (rootWaveTuple .full)) ω
    have hh := full_response_identity_wave_reconstruction M Q N hN weights k (H ω) hge ω
    change fullResponseIdentityWaveTerm M Q N weights k ω = _ at hh
    rw [hh]
    dsimp only [C,D,f,W]
    ring
  rw [he]
  refine ⟨((hm 0).const_mul _).add ((hm 1).const_mul _), ?_⟩
  have hh := full_response_linear_family_Lp (Cutoff.cutoffSampleLaw M).toMeasure
    (ENNReal.ofReal p) (ENNReal.one_le_ofReal.mpr (by linarith only [hp])) (W 0) (W 1)
    (C*(D+f)) C (physicalSelectedWaveBudget M.gamma p 377 0)
    (physicalSelectedWaveBudget M.gamma p 377 1) (mul_nonneg hC hDf) hC
    (full_response_selected_wave_budget_nonneg _ _ (by linarith only [hp]) _)
    (full_response_selected_wave_budget_nonneg _ _ (by linarith only [hp]) _) (hb 0) (hb 1)
  apply hh.trans_eq
  congr 1
  dsimp only [fullResponseIdentityWaveTermBudget,C,D,f]
  ring

/-- The complete actual selected identity-wave series is absolutely summable
a.e. and pays exactly the source identity coefficients, including A_f. -/
theorem full_response_identity_wave_series_Lp
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (Q : TriadicCube 2)
    (hpast : ∀ n ≤ Q.scale-337, nativeInductionState M h n)
    (N : ℤ) (hN : Q.scale-1 ≤ N) (weights : ℤ → ℝ)
    (hw : ∀ j ∈ Finset.Ioc (Q.scale-342) N, 0 ≤ weights j ∧ weights j ≤ 1)
    (p : ℝ) (hp : 2 ≤ p) (hp256 : p ≤ 256) :
    let D := (N:ℝ)-(Q.scale:ℝ)+1
    let F := fullResponseIdentityWaveTerm M Q N weights
    (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure, Summable (fun k => ‖F k ω‖)) ∧
      eLpNorm (fun ω => ∑' k, F k ω) (ENNReal.ofReal p)
        (Cutoff.cutoffSampleLaw M).toMeasure ≤ ENNReal.ofReal
          ((M.gamma*(3:ℝ)^(2*M.gamma*D)/4)*
            (physicalSelectedWaveBudget M.gamma p 377 0*
              (D*fullResponseWaveLayerMass M.gamma+fullResponseWaveLayerFirst M.gamma)+
              physicalSelectedWaveBudget M.gamma p 377 1*fullResponseWaveLayerMass M.gamma)) := by
  let D := (N:ℝ)-(Q.scale:ℝ)+1
  have hb (k : ℕ) := full_response_identity_wave_term_Lp M h hM hg Q hpast N hN weights hw k p hp hp256
  have hD : 0 ≤ D := by dsimp only [D]; exact_mod_cast (show 0 ≤ N-Q.scale+1 by omega)
  have hc (k : ℕ) : 0 ≤ fullResponseIdentityWaveTermBudget M.gamma p D k := by
    have hγ := M.shellPrefix.gamma_pos.le
    have hv := bankLayerWeight_nonneg k
    have h0 := full_response_selected_wave_budget_nonneg M.gamma p (by linarith only [hp]) 0
    have h1 := full_response_selected_wave_budget_nonneg M.gamma p (by linarith only [hp]) 1
    dsimp only [fullResponseIdentityWaveTermBudget]
    positivity
  exact countable_density_series_Lp (Cutoff.cutoffSampleLaw M).toMeasure
    (ENNReal.ofReal p) (ENNReal.one_le_ofReal.mpr (by linarith only [hp]))
    (fullResponseIdentityWaveTerm M Q N weights) (fun k => (hb k).1)
    (fullResponseIdentityWaveTermBudget M.gamma p D) hc _
    (full_response_identity_wave_budget_hasSum M.gamma D
      (physicalSelectedWaveBudget M.gamma p 377 0) (physicalSelectedWaveBudget M.gamma p 377 1) hg)
    (fun k => (hb k).2)

end
end ASDExplicitGamma.Inverse
