module

public import ASDExplicitGamma.Cold.PlateauProjectionSplit

/-! # CO-PLATEAU-P6: direct fine-depth Gram bound and its history charge -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization
open ASDExplicitGamma.Triadic
open scoped BigOperators
namespace ASDExplicitGamma.Cold

/-- P3 on restricted terminal fields uses the terminal energy, without an own-cell gap. -/
theorem square_projected_graph_gram (Q : TriadicCube 2) {a : CoeffField 2} {lam Lam η M : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a) (hη : 0 < η)
    (v : SquareMatchedOptimizers Q a) (r : ℕ)
    (hmax : ∀ R : SquareCells Q r, traceDefect (openCubeSet R.val) a 1 ≤ M) :
    squareProjectedGraphEnergy Q hEll v r ≤
      (2*(1+η)+(2+1/(4*η))*M)*(2*traceDefect (openCubeSet Q) a 1) := by
  let C := 2*(1+η)+(2+1/(4*η))*M
  have hc (R : SquareCells Q r) :
      squareFourGraphEnergy R.val
        (fun i => squareCellRestriction Q hEll (v.primal i) R)
        (fun i => squareCellRestriction Q (isEllipticFieldOn_adjointCoeffField hEll) (v.adjoint i) R) ≤
      C*(∑ i : Fin 2, (volumeAverage (openCubeSet R.val) (scalarVariationEnergyIntegrand a (v.primal i)) +
        volumeAverage (openCubeSet R.val) (scalarVariationEnergyIntegrand (adjointCoeffField a) (v.adjoint i)))) := by
    let hER := hEll.mono (measurableSet_openCubeSet R.val) (openCubeSet_subset_of_mem_descendantsAtDepth R.property)
    have h := square_four_graph_gram R.val hER hη
      (fun i => squareCellRestriction Q hEll (v.primal i) R)
      (fun i => squareCellRestriction Q (isEllipticFieldOn_adjointCoeffField hEll) (v.adjoint i) R)
    refine h.trans (mul_le_mul_of_nonneg_right
      (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (hmax R) (by positivity))) ?_)
    apply Finset.sum_nonneg
    intro i _
    exact add_nonneg
      (volumeAverage_scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn _ _ hER _)
      (volumeAverage_scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn _ _
        (isEllipticFieldOn_adjointCoeffField hER) _)
  have h := squareCellMean_mono Q r hc
  rw [squareCellMean_mul,squareCellMean_sum] at h
  simp_rw [squareCellMean_add,
    squareCellMean_volumeAverage Q r ((ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll).energy _),
    squareCellMean_volumeAverage Q r ((ResponseLinearIntegrabilityData.of_isEllipticFieldOn
      (isEllipticFieldOn_adjointCoeffField hEll)).energy _)] at h
  rw [square_matched_optimizer_energy Q hEll v.primal v.adjoint v.primal_max v.adjoint_max] at h
  exact h

/-- CO-PLATEAU-P6 with the depth multiplier `s=3^(r/4)`. The depth-zero history
bound controls the actual terminal trace, giving one power of `s` in the bad charge. -/
theorem plateau_fine_tail {Q : TriadicCube 2} {r : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {ℙ : Measure Ω} [IsFiniteMeasure ℙ]
    (F : ColdRecoveryFamily Q r Ω) {D : Ω → ℝ} {s η ξ H : ℝ}
    (hs : 0 ≤ s) (hη : 0 < η) (hξ : 0 < ξ)
    (hD : Measurable D) (hDn : ∀ᵐ ω ∂ℙ, 0 ≤ D ω)
    (h20 : Integrable (fun ω => D ω^20) ℙ) (hMoment : (∫ ω, D ω^20 ∂ℙ) ≤ H^20)
    (hp : Integrable F.parentTrace ℙ)
    (hroot : ∀ᵐ ω ∂ℙ, F.parentTrace ω ≤ D ω)
    (hmax : ∀ᵐ ω ∂ℙ, ∀ R, F.cellTrace R ω ≤ s*D ω) :
    (∫ ω, squareProjectedGraphEnergy Q (F.elliptic ω) (F.parent ω) r ∂ℙ) ≤
      2*(2*(1+η)+(2+1/(4*η))*s*ξ)*(∫ ω, F.parentTrace ω ∂ℙ) +
      2*(2+1/(4*η))*s*H^20/ξ^18 := by
  let Z := fun ω => 2*F.parentTrace ω
  let g0 := 2*(1+η)
  let g1 := 2+1/(4*η)
  have hg0 : 0 ≤ g0 := by dsimp [g0]; positivity
  have hg1 : 0 ≤ g1 := by dsimp [g1]; positivity
  have hz : Integrable Z ℙ := hp.const_mul 2
  have hzn : ∀ᵐ ω ∂ℙ, 0 ≤ Z ω := Filter.Eventually.of_forall (fun ω =>
    mul_nonneg (by norm_num) (coarse_square_traceDefect_nonneg Q (F.elliptic ω)))
  have hb : ∀ᵐ ω ∂ℙ, Z ω ≤ 2*1*D ω := by
    filter_upwards [hroot] with ω hω
    dsimp only [Z]
    linarith only [hω]
  have hprod := integrable_history_product hD hz hDn hzn hg0 hg1 hs (by norm_num : (0:ℝ) ≤ 1) hb h20
  have hh := expected_history_product_le hD hz hDn hzn hg0 hg1 hs (by norm_num : (0:ℝ) ≤ 1) hξ hb h20 hMoment
  have hvnon : ∀ᵐ ω ∂ℙ, 0 ≤ squareProjectedGraphEnergy Q (F.elliptic ω) (F.parent ω) r :=
    Filter.Eventually.of_forall (fun ω => by
      have h := squareCellMean_mono Q r (fun R => squareFourGraphEnergy_nonneg R.val
        (fun i => squareCellRestriction Q (F.elliptic ω) ((F.parent ω).primal i) R)
        (fun i => squareCellRestriction Q (isEllipticFieldOn_adjointCoeffField (F.elliptic ω))
          ((F.parent ω).adjoint i) R))
      rw [squareCellMean_const] at h
      exact h)
  have hv := integral_mono_of_nonneg hvnon hprod (show ∀ᵐ ω ∂ℙ,
      squareProjectedGraphEnergy Q (F.elliptic ω) (F.parent ω) r ≤ (g0+g1*s*D ω)*Z ω from by
    filter_upwards [hmax] with ω hω
    simpa only [g0,g1,Z,ColdRecoveryFamily.parentTrace,mul_assoc] using
      square_projected_graph_gram Q (F.elliptic ω) hη (F.parent ω) r hω)
  have hzint : (∫ ω, Z ω ∂ℙ) = 2*(∫ ω, F.parentTrace ω ∂ℙ) := integral_const_mul _ _
  rw [hzint] at hh
  dsimp only [g0,g1] at hh hv
  calc
    _ ≤ _ := hv.trans hh
    _ = _ := by ring

/-- CO-PLATEAU-P6 in the displayed source depth normalization. -/
theorem plateau_fine_tail_depth {Q : TriadicCube 2} {r : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {ℙ : Measure Ω} [IsFiniteMeasure ℙ]
    (F : ColdRecoveryFamily Q r Ω) {D : Ω → ℝ} {η ξ H : ℝ}
    (hη : 0 < η) (hξ : 0 < ξ)
    (hD : Measurable D) (hDn : ∀ᵐ ω ∂ℙ, 0 ≤ D ω)
    (h20 : Integrable (fun ω => D ω^20) ℙ) (hMoment : (∫ ω, D ω^20 ∂ℙ) ≤ H^20)
    (hp : Integrable F.parentTrace ℙ)
    (hroot : ∀ᵐ ω ∂ℙ, F.parentTrace ω ≤ D ω)
    (hmax : ∀ᵐ ω ∂ℙ, ∀ R, F.cellTrace R ω ≤ (3:ℝ)^((r:ℝ)/4)*D ω) :
    (∫ ω, squareProjectedGraphEnergy Q (F.elliptic ω) (F.parent ω) r ∂ℙ) ≤
      2*(2*(1+η)+(2+1/(4*η))*ξ*(3:ℝ)^((r:ℝ)/4))*(∫ ω, F.parentTrace ω ∂ℙ) +
      2*(2+1/(4*η))*(3:ℝ)^((r:ℝ)/4)*H^20/ξ^18 := by
  have h := plateau_fine_tail F (s := (3:ℝ)^((r:ℝ)/4))
    (Real.rpow_nonneg (by norm_num) _) hη hξ hD hDn h20 hMoment hp hroot hmax
  convert h using 1
  ring

end ASDExplicitGamma.Cold
