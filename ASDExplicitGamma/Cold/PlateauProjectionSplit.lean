module

public import ASDExplicitGamma.Cold.ProjectedGraphGram
public import ASDExplicitGamma.Cold.ColdRecoveryFamily
public import ASDExplicitGamma.Cold.GoodBadHistory

/-! # CO-PLATEAU-P5: actual projected fields and correlated history -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization
open ASDExplicitGamma.Triadic
namespace ASDExplicitGamma.Cold

/-- The actual own-cell-minus-parent trace drop. -/
def ColdRecoveryFamily.energyDrop {Q : TriadicCube 2} {r : ℕ} {Ω : Type*}
    (F : ColdRecoveryFamily Q r Ω) (ω : Ω) : ℝ :=
  2*(squareCellMean Q r (fun R => F.cellTrace R ω)-F.parentTrace ω)

/-- Ordinary source integrability and stationarity identify the expected projection drop. -/
theorem ColdRecoveryFamily.integral_energyDrop {Q : TriadicCube 2} {r : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {ℙ : Measure Ω} (F : ColdRecoveryFamily Q r Ω)
    (hp : Integrable F.parentTrace ℙ) (hf : ∀ R, Integrable (F.cellTrace R) ℙ)
    {μ : ℝ} (hstat : ∀ R, ∫ ω, F.cellTrace R ω ∂ℙ = μ) :
    (∫ ω, F.energyDrop ω ∂ℙ) = 2*(μ-∫ ω, F.parentTrace ω ∂ℙ) := by
  unfold ColdRecoveryFamily.energyDrop
  rw [integral_const_mul,integral_sub (integrable_squareCellMean Q r hf) hp,
    integral_squareCellMean Q r hf]
  simp_rw [hstat]
  rw [squareCellMean_const]

/-- CO-PLATEAU-P5 with the depth multiplier written as `s` (the source uses `3^(r/4)`).
The graph and energy-drop quantities are defined from the actual harmonic optimizers;
no projection estimate or independence is assumed. -/
theorem plateau_projection_split {Q : TriadicCube 2} {r : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {ℙ : Measure Ω} [IsFiniteMeasure ℙ]
    (F : ColdRecoveryFamily Q r Ω) {D : Ω → ℝ} {s t η ξ H μsmall : ℝ}
    (hs : 0 ≤ s) (ht : 0 < t) (hη : 0 < η) (hξ : 0 < ξ)
    (hD : Measurable D) (hDn : ∀ᵐ ω ∂ℙ, 0 ≤ D ω)
    (h20 : Integrable (fun ω => D ω^20) ℙ) (hMoment : (∫ ω, D ω^20 ∂ℙ) ≤ H^20)
    (hp : Integrable F.parentTrace ℙ) (hf : ∀ R, Integrable (F.cellTrace R) ℙ)
    (hstat : ∀ R, ∫ ω, F.cellTrace R ω ∂ℙ = μsmall)
    (hmax : ∀ᵐ ω ∂ℙ, ∀ R, F.cellTrace R ω ≤ s*D ω)
    (hG : Integrable (fun ω => squareOwnGraphEnergy Q (F.cells ω)) ℙ) :
    (∫ ω, squareProjectedGraphEnergy Q (F.elliptic ω) (F.parent ω) r ∂ℙ) ≤
      2*(1+1/t)*(2*(1+η)+(2+1/(4*η))*s*ξ)*(μsmall-∫ ω, F.parentTrace ω ∂ℙ) +
      (1+t)*(∫ ω, squareOwnGraphEnergy Q (F.cells ω) ∂ℙ) +
      2*(2+1/(4*η))*(1+1/t)*s^2*H^20/ξ^18 := by
  let g0 := 2*(1+η)
  let g1 := 2+1/(4*η)
  have hg0 : 0 ≤ g0 := by dsimp [g0]; positivity
  have hg1 : 0 ≤ g1 := by dsimp [g1]; positivity
  have ht' : 0 ≤ 1+1/t := by positivity
  have hz : Integrable F.energyDrop ℙ :=
    ((integrable_squareCellMean Q r hf).sub hp).const_mul 2
  have hb : ∀ᵐ ω ∂ℙ, 0 ≤ F.energyDrop ω ∧ F.energyDrop ω ≤ 2*s*D ω := by
    filter_upwards [hmax] with ω hω
    simpa only [ColdRecoveryFamily.energyDrop,ColdRecoveryFamily.cellTrace,
      ColdRecoveryFamily.parentTrace,mul_assoc] using
      square_energy_drop_bounds Q (F.elliptic ω) (F.parent ω) (F.cells ω) hω
  have hZn := hb.mono (fun _ h => h.1)
  have hbound := hb.mono (fun _ h => h.2)
  have hprod := integrable_history_product hD hz hDn hZn hg0 hg1 hs hs hbound h20
  have hhistory := expected_history_product_le hD hz hDn hZn hg0 hg1 hs hs hξ hbound h20 hMoment
  have hupper : Integrable (fun ω => (1+t)*squareOwnGraphEnergy Q (F.cells ω) +
      (1+1/t)*((g0+g1*s*D ω)*F.energyDrop ω)) ℙ :=
    (hG.const_mul _).add (hprod.const_mul _)
  have hpoint : ∀ᵐ ω ∂ℙ, squareProjectedGraphEnergy Q (F.elliptic ω) (F.parent ω) r ≤
      (1+t)*squareOwnGraphEnergy Q (F.cells ω)+(1+1/t)*((g0+g1*s*D ω)*F.energyDrop ω) := by
    filter_upwards [hmax] with ω hω
    have hsplit := square_projected_graph_split Q (F.elliptic ω) ht (F.parent ω) (F.cells ω)
    have hgram := square_residual_graph_gram Q (F.elliptic ω) hη (F.parent ω) (F.cells ω) hω
    have hm := mul_le_mul_of_nonneg_left hgram ht'
    dsimp only [g0,g1,ColdRecoveryFamily.energyDrop,ColdRecoveryFamily.cellTrace,
      ColdRecoveryFamily.parentTrace] at *
    linarith only [hsplit,hm]
  have hvnon : ∀ᵐ ω ∂ℙ, 0 ≤ squareProjectedGraphEnergy Q (F.elliptic ω) (F.parent ω) r :=
    Filter.Eventually.of_forall (fun ω => by
      have h := squareCellMean_mono Q r (fun R => squareFourGraphEnergy_nonneg R.val
        (fun i => squareCellRestriction Q (F.elliptic ω) ((F.parent ω).primal i) R)
        (fun i => squareCellRestriction Q (isEllipticFieldOn_adjointCoeffField (F.elliptic ω))
          ((F.parent ω).adjoint i) R))
      rw [squareCellMean_const] at h
      exact h)
  have hv := integral_mono_of_nonneg hvnon hupper hpoint
  rw [integral_add (hG.const_mul _) (hprod.const_mul _),integral_const_mul,integral_const_mul] at hv
  rw [F.integral_energyDrop hp hf hstat] at hhistory
  have hm := mul_le_mul_of_nonneg_left hhistory ht'
  dsimp only [g0,g1] at hv hm
  have heq : (1+1/t)*((2*(1+η)+(2+1/(4*η))*s*ξ)*
      (2*(μsmall-∫ ω, F.parentTrace ω ∂ℙ))+2*(2+1/(4*η))*s*s*H^20/ξ^18) =
      2*(1+1/t)*(2*(1+η)+(2+1/(4*η))*s*ξ)*(μsmall-∫ ω, F.parentTrace ω ∂ℙ)+
      2*(2+1/(4*η))*(1+1/t)*s^2*H^20/ξ^18 := by ring
  rw [heq] at hm
  linarith only [hv,hm]

/-- CO-PLATEAU-P5 in the displayed source depth normalization. -/
theorem plateau_projection_split_depth {Q : TriadicCube 2} {r : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {ℙ : Measure Ω} [IsFiniteMeasure ℙ]
    (F : ColdRecoveryFamily Q r Ω) {D : Ω → ℝ} {t η ξ H μsmall : ℝ}
    (ht : 0 < t) (hη : 0 < η) (hξ : 0 < ξ)
    (hD : Measurable D) (hDn : ∀ᵐ ω ∂ℙ, 0 ≤ D ω)
    (h20 : Integrable (fun ω => D ω^20) ℙ) (hMoment : (∫ ω, D ω^20 ∂ℙ) ≤ H^20)
    (hp : Integrable F.parentTrace ℙ) (hf : ∀ R, Integrable (F.cellTrace R) ℙ)
    (hstat : ∀ R, ∫ ω, F.cellTrace R ω ∂ℙ = μsmall)
    (hmax : ∀ᵐ ω ∂ℙ, ∀ R, F.cellTrace R ω ≤ (3:ℝ)^((r:ℝ)/4)*D ω)
    (hG : Integrable (fun ω => squareOwnGraphEnergy Q (F.cells ω)) ℙ) :
    (∫ ω, squareProjectedGraphEnergy Q (F.elliptic ω) (F.parent ω) r ∂ℙ) ≤
      2*(1+1/t)*(2*(1+η)+(2+1/(4*η))*ξ*(3:ℝ)^((r:ℝ)/4))*(μsmall-∫ ω, F.parentTrace ω ∂ℙ) +
      (1+t)*(∫ ω, squareOwnGraphEnergy Q (F.cells ω) ∂ℙ) +
      2*(2+1/(4*η))*(1+1/t)*(3:ℝ)^((r:ℝ)/2)*H^20/ξ^18 := by
  have he : ((3:ℝ)^((r:ℝ)/4))^2 = (3:ℝ)^((r:ℝ)/2) := by
    rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 3)]
    congr 1
    ring
  have h := plateau_projection_split F (s := (3:ℝ)^((r:ℝ)/4))
    (Real.rpow_nonneg (by norm_num) _) ht hη hξ hD hDn h20 hMoment hp hf hstat hmax hG
  rw [he] at h
  convert h using 1
  ring

end ASDExplicitGamma.Cold
