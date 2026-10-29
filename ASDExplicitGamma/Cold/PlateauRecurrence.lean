module

public import ASDExplicitGamma.Cold.ExpectedPlateauTransport
public import ASDExplicitGamma.Cold.PlateauCutoffRecovery
public import ASDExplicitGamma.Cold.PlateauRecurrenceCoefficients

/-! # CO-PLATEAU-RECURRENCE from the actual P1--P6 estimates -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization
open ASDExplicitGamma.Triadic
open scoped BigOperators
namespace ASDExplicitGamma.Cold

/-- CO-PLATEAU-RECURRENCE at an even lag `j=2J`. `μsmall r` is the expected ordinary
trace on the actual depth-r cells, hence the source `μ_(j-r)`. All harmonic fields,
cutoff energies, and projected graph terms are actual quantities. The history bounds
and own-cell graph integrability are source inputs; no recurrence or transport estimate
is assumed. The generic `r4=4` binder avoids expanding the depth-four cell type. -/
theorem plateau_recurrence {Q : TriadicCube 2} {Ω : Type*}
    [MeasurableSpace Ω] {ℙ : Measure Ω} [IsFiniteMeasure ℙ]
    (F : ColdPlateauFamily Q Ω) {J r4 : ℕ} (hJ : 2 ≤ J) (hr4 : r4 = 4)
    {c t η ξ H : ℝ} (hc : 0 < c) (hc1 : c < 1) (ht : 0 < t) (hη : 0 < η) (hξ : 0 < ξ)
    {D : Ω → ℝ} (hD : Measurable D) (hDn : ∀ᵐ ω ∂ℙ, 0 ≤ D ω)
    (h20 : Integrable (fun ω => D ω^20) ℙ) (hMoment : (∫ ω, D ω^20 ∂ℙ) ≤ H^20)
    (hV : ∀ k, AEStronglyMeasurable (F.projectedGraph (2*(k+1))) ℙ)
    (hroot : ∀ᵐ ω ∂ℙ, (F.atDepth 0).parentTrace ω ≤ D ω)
    (hmax : ∀ᵐ ω ∂ℙ, ∀ r, ∀ R, (F.atDepth r).cellTrace R ω ≤ (3:ℝ)^((r:ℝ)/4)*D ω)
    (hInt4 : ColdRecoveryIntegrable (F.atDepth r4) ℙ)
    (hcell : ∀ r R, Integrable ((F.atDepth r).cellTrace R) ℙ)
    (hG : ∀ k < J, Integrable (fun ω => squareOwnGraphEnergy Q (F.cells (2*(k+1)) ω)) ℙ)
    {μsmall : ℕ → ℝ} (hstat : ∀ r R, ∫ ω, (F.atDepth r).cellTrace R ω ∂ℙ = μsmall r) :
    let CT := 4/(7*(1-c))
    let CD := 96/(49*c)-1
    let g0 := 2*(1+η)
    let g1 := 2+1/(4*η)
    let α := 1+1/t
    let μ := ∫ ω, (F.atDepth 0).parentTrace ω ∂ℙ
    (1+(∑ k ∈ Finset.range J, plateauLagCoefficient CT CD α g0 g1 ξ k)-
      plateauFineCoefficient CT g0 g1 ξ J)*μ ≤
      (∑ k ∈ Finset.range J, plateauLagCoefficient CT CD α g0 g1 ξ k*μsmall (2*(k+1)))+
      CT*(1+t)*(∑ k ∈ Finset.range J, plateauEvenWeight k*
        (∫ ω, squareOwnGraphEnergy Q (F.cells (2*(k+1)) ω) ∂ℙ))+
      (55/4)*CT*g1*α*H^20/ξ^18 := by
  dsimp only
  let CT := 4/(7*(1-c))
  let CD := 96/(49*c)-1
  let g0 := 2*(1+η)
  let g1 := 2+1/(4*η)
  let α := 1+1/t
  let μ := ∫ ω, (F.atDepth 0).parentTrace ω ∂ℙ
  let μlag := fun k => μsmall (2*(k+1))
  let V := fun k => ∫ ω, F.projectedGraph (2*(k+1)) ω ∂ℙ
  let X := fun k => plateauEvenWeight k*V k
  let C := plateauGramWeight g0 g1 ξ
  let B := fun k => (2*g1*α*H^20/ξ^18)*(plateauEvenWeight k*(3:ℝ)^(k+1))
  let G := fun k => plateauEvenWeight k*(∫ ω, squareOwnGraphEnergy Q (F.cells (2*(k+1)) ω) ∂ℙ)
  have hCT : 0 ≤ CT := by dsimp [CT]; positivity
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hg1 : 0 ≤ g1 := by dsimp [g1]; positivity
  have hX : Summable X := (F.weightedGraph_expectation hD hDn h20 hV hroot hmax).2.1
  have hC : Summable C := summable_plateauGramWeight g0 g1 ξ
  have hB : Summable B := summable_plateauEvenWeight_three.mul_left _
  have hp : Integrable (F.atDepth 0).parentTrace ℙ := hInt4.parentTrace
  have hnear (k : ℕ) (hk : k < J) : X k ≤ 2*α*C k*(μlag k-μ)+(1+t)*G k+B k := by
    have h := plateau_projection_split_depth (F.atDepth (2*(k+1))) ht hη hξ hD hDn h20 hMoment
      hp (hcell _) (hstat _) (hmax.mono fun ω h => h _) (hG k hk)
    have hw := mul_le_mul_of_nonneg_left h (plateauEvenWeight_nonneg k)
    rw [plateau_even_depth_factor] at hw
    have he : (3:ℝ)^(((2*(k+1):ℕ):ℝ)/2) = (3:ℝ)^(k+1) := by
      rw [← Real.rpow_natCast]
      congr 1
      push_cast
      ring
    rw [he] at hw
    dsimp only [X,V,ColdPlateauFamily.projectedGraph,C,plateauGramWeight,μlag,μ,G,B,α,g0,g1]
    dsimp only [ColdPlateauFamily.atDepth,ColdRecoveryFamily.parentTrace] at hw ⊢
    convert hw using 1
    ring
  have hfar (k : ℕ) : X (k+J) ≤ 2*C (k+J)*μ+B (k+J) := by
    have h := plateau_fine_tail_depth (F.atDepth (2*(k+J+1))) hη hξ hD hDn h20 hMoment hp hroot
      (hmax.mono fun ω h => h _)
    have hw := mul_le_mul_of_nonneg_left h (plateauEvenWeight_nonneg (k+J))
    rw [plateau_even_depth_factor] at hw
    have hs : 1 ≤ (Real.sqrt 3)^(k+J+1) := one_le_pow₀ (by
      apply (Real.le_sqrt (by norm_num) (by norm_num)).mpr
      norm_num)
    have hcharge :
        2*g1*(Real.sqrt 3)^(k+J+1)*H^20/ξ^18 ≤
        (2*g1*α*H^20/ξ^18)*(3:ℝ)^(k+J+1) := by
      have hs2 : ((Real.sqrt 3)^(k+J+1))^2 = (3:ℝ)^(k+J+1) := by
        rw [pow_right_comm,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
      have hα1 : 1 ≤ α := by dsimp [α]; exact le_add_of_nonneg_right (div_nonneg (by norm_num) ht.le)
      have hmul : (Real.sqrt 3)^(k+J+1) ≤ α*((Real.sqrt 3)^(k+J+1))^2 := by
        nlinarith only [hs,hα1,sq_nonneg ((Real.sqrt 3)^(k+J+1)-1),
          mul_nonneg (sub_nonneg.mpr hα1) (sq_nonneg ((Real.sqrt 3)^(k+J+1)))]
      rw [hs2] at hmul
      have hb := mul_le_mul_of_nonneg_left hmul
        (show 0 ≤ 2*g1*H^20/ξ^18 by positivity)
      convert hb using 1 <;> ring
    have hm := mul_le_mul_of_nonneg_left hcharge (plateauEvenWeight_nonneg (k+J))
    dsimp only [X,V,ColdPlateauFamily.projectedGraph,C,plateauGramWeight,μ,B,g0,g1] at *
    dsimp only [ColdPlateauFamily.atDepth,ColdRecoveryFamily.parentTrace] at hw ⊢
    nlinarith only [hw,hm]
  have htransport := expected_plateau_matched_energy_le F hD hDn h20 hV hroot hmax
  have hrecover := plateau_cutoff_recovery_constants (F.atDepth r4) hInt4 hr4 hc hc1 (hstat r4)
  have hrecovery : μ ≤ CT*(∑' k, X k)+CD*(μlag 1-μ) := by
    have hm := mul_le_mul_of_nonneg_left htransport hCT
    change μ ≤ CT*(∫ ω, (F.atDepth 0).parentCutoffEnergy ω ∂ℙ)+CD*(μsmall r4-μ) at hrecover
    rw [hr4] at hrecover
    change _ ≤ CT*(∑' k, X k) at hm
    dsimp only [μlag]
    norm_num only at *
    linarith only [hm,hrecover]
  have h := plateau_recurrence_rearrange hCT hX hC hB hnear hfar hrecovery
  have hbad : CT*(∑' k, B k) = (55/4)*CT*g1*α*H^20/ξ^18 := plateau_bad_charge CT g1 α H ξ
  rw [hbad] at h
  change (1+(∑ k ∈ Finset.range J, plateauLagCoefficient CT CD α g0 g1 ξ k)-
    plateauFineCoefficient CT g0 g1 ξ J)*μ ≤
    (∑ k ∈ Finset.range J, plateauLagCoefficient CT CD α g0 g1 ξ k*μlag k)+
    CT*(1+t)*(∑ k ∈ Finset.range J, G k)+(55/4)*CT*g1*α*H^20/ξ^18
  rw [sum_plateauLagCoefficient hJ,sum_plateauLagCoefficient_mul hJ]
  dsimp only [C] at h
  dsimp only [plateauFineCoefficient]
  convert h using 1
  ring

end ASDExplicitGamma.Cold
