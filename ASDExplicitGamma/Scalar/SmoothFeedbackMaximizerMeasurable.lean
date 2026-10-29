/-
Copyright (c) 2026 Scott N. Armstrong. All rights reserved.
-/
module

public import ASDExplicitGamma.Scalar.SmoothFeedbackGapMeasurable

/-! Measurability of the actual OLD maximizer as an `L²` class. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization Response Triadic Variational Filter Topology
open ASDExplicitGamma.Native
open Algsuperdiff.Section3
open scoped BigOperators

noncomputable section

/-- Abstract argmax measurability: the maximizer of a measurable family of strictly
coercive symmetric quadratic functionals over a fixed linear subspace of a separable
Hilbert space is measurable in the parameter. -/
theorem argmax_measurable
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace (E →L[ℝ] E →L[ℝ] ℝ)]
    (B : Ω → E →L[ℝ] E →L[ℝ] ℝ) (hB : Measurable B)
    (hev : ∀ T : E, Measurable fun ω => B ω T T)
    (hsymm : ∀ ω x y, B ω x y = B ω y x)
    (hcoer : ∀ ω, ∃ C : ℝ, 0 < C ∧ ∀ x, C * ‖x‖ * ‖x‖ ≤ B ω x x)
    (ℓ : E →L[ℝ] ℝ) (S : Submodule ℝ E) (Z : Ω → E)
    (hZS : ∀ ω, Z ω ∈ S)
    (hmax : ∀ ω, ∀ T ∈ S, 2 * ℓ T - B ω T T ≤ 2 * ℓ (Z ω) - B ω (Z ω) (Z ω)) :
    Measurable Z := by
  classical
  have hJ := maximal_value_measurable B hB hev ℓ (S : Set E) Z hZS hmax
  -- Euler equation on the subspace
  have heuler : ∀ ω, ∀ Y ∈ S, ℓ Y = B ω (Z ω) Y := by
    intro ω Y hY
    have hpoly : ∀ t : ℝ, 2 * t * (ℓ Y - B ω (Z ω) Y) - t ^ 2 * B ω Y Y ≤ 0 := by
      intro t
      have h := hmax ω (Z ω + t • Y) (S.add_mem (hZS ω) (S.smul_mem t hY))
      have e1 : B ω (Z ω + t • Y) (Z ω + t • Y) =
          B ω (Z ω) (Z ω) + 2 * t * B ω (Z ω) Y + t ^ 2 * B ω Y Y := by
        simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
          ContinuousLinearMap.smul_apply, smul_eq_mul]
        rw [hsymm ω Y (Z ω)]
        ring
      rw [map_add, map_smul, e1, smul_eq_mul] at h
      linarith
    have ha : 0 ≤ B ω Y Y := by
      obtain ⟨C, hC, h⟩ := hcoer ω
      exact le_trans (by positivity) (h Y)
    by_contra hne
    have hc : ℓ Y - B ω (Z ω) Y ≠ 0 := fun h => hne (by linarith)
    have hc2 : 0 < (ℓ Y - B ω (Z ω) Y) ^ 2 := by positivity
    have h1 := hpoly ((ℓ Y - B ω (Z ω) Y) / (B ω Y Y + 1))
    have hpos : 0 < B ω Y Y + 1 := by linarith
    have h2 : 2 * ((ℓ Y - B ω (Z ω) Y) / (B ω Y Y + 1)) * (ℓ Y - B ω (Z ω) Y) -
        ((ℓ Y - B ω (Z ω) Y) / (B ω Y Y + 1)) ^ 2 * B ω Y Y =
        (ℓ Y - B ω (Z ω) Y) ^ 2 * (B ω Y Y + 2) / (B ω Y Y + 1) ^ 2 := by
      field_simp
      ring
    rw [mul_assoc, mul_comm] at h1
    have : 0 < (ℓ Y - B ω (Z ω) Y) ^ 2 * (B ω Y Y + 2) / (B ω Y Y + 1) ^ 2 := by positivity
    nlinarith [h1, h2, this]
  -- a dense sequence in the subspace
  haveI : Nonempty S := ⟨⟨0, S.zero_mem⟩⟩
  obtain ⟨T, hTd⟩ := TopologicalSpace.exists_dense_seq S
  let Tn : ℕ → E := fun n => (T n : E)
  let J : Ω → E → ℝ := fun ω x => 2 * ℓ x - B ω x x
  let d : ℕ → Ω → ℝ := fun n ω => (2 * ℓ (Z ω) - B ω (Z ω) (Z ω)) - J ω (Tn n)
  have hdm : ∀ n, Measurable (d n) := fun n =>
    hJ.sub (measurable_const.sub (hev (Tn n)))
  have hdeq : ∀ n ω, d n ω = B ω (Z ω - Tn n) (Z ω - Tn n) := by
    intro n ω
    have h1 := heuler ω (Tn n) (T n).2
    simp only [d, J]
    have e : B ω (Z ω - Tn n) (Z ω - Tn n) = B ω (Z ω) (Z ω) - B ω (Z ω) (Tn n) -
        B ω (Tn n) (Z ω) + B ω (Tn n) (Tn n) := by
      simp only [map_sub, ContinuousLinearMap.sub_apply]
      ring
    rw [e, hsymm ω (Tn n) (Z ω), ← h1]
    have h2 := heuler ω (Z ω) (hZS ω)
    linarith
  have hdlow : ∀ n ω, ∃ C : ℝ, 0 < C ∧ C * ‖Z ω - Tn n‖ * ‖Z ω - Tn n‖ ≤ d n ω := by
    intro n ω
    obtain ⟨C, hC, h⟩ := hcoer ω
    exact ⟨C, hC, by rw [hdeq]; exact h _⟩
  have hex : ∀ k : ℕ, ∀ ω, ∃ n, d n ω < 1 / ((k : ℝ) + 1) := by
    intro k ω
    have hcont : Continuous fun x : E => J ω x :=
      (continuous_const.mul ℓ.continuous).sub ((B ω).continuous.clm_apply continuous_id)
    have hopen : IsOpen {x : S | (2 * ℓ (Z ω) - B ω (Z ω) (Z ω)) - 1 / ((k : ℝ) + 1) <
        J ω x} :=
      isOpen_lt continuous_const (hcont.comp continuous_subtype_val)
    have hmem : (⟨Z ω, hZS ω⟩ : S) ∈ {x : S | (2 * ℓ (Z ω) - B ω (Z ω) (Z ω)) -
        1 / ((k : ℝ) + 1) < J ω x} := by
      change _ < _
      have : 0 < 1 / ((k : ℝ) + 1) := by positivity
      simp only [J]
      linarith
    obtain ⟨n, hn⟩ := hTd.exists_mem_open hopen ⟨_, hmem⟩
    refine ⟨n, ?_⟩
    simp only [d]
    have hn' : (2 * ℓ (Z ω) - B ω (Z ω) (Z ω)) - 1 / ((k : ℝ) + 1) < J ω (Tn n) := hn
    linarith
  let nk : ℕ → Ω → ℕ := fun k ω => Nat.find (hex k ω)
  have hnk : ∀ k, Measurable (nk k) := fun k =>
    measurable_find (hex k) fun n => measurableSet_lt (hdm n) measurable_const
  let Zk : ℕ → Ω → E := fun k ω => Tn (nk k ω)
  have hZk : ∀ k, Measurable (Zk k) := fun k =>
    (measurable_from_nat (f := Tn)).comp (hnk k)
  refine measurable_of_tendsto_metrizable hZk ?_
  rw [tendsto_pi_nhds]
  intro ω
  obtain ⟨C, hC, hCle⟩ := hcoer ω
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq : ∀ k : ℕ, ‖Zk k ω - Z ω‖ ^ 2 ≤ 1 / (C * ((k : ℝ) + 1)) := by
    intro k
    have h1 : d (nk k ω) ω < 1 / ((k : ℝ) + 1) := Nat.find_spec (hex k ω)
    have h2 := hCle (Z ω - Tn (nk k ω))
    rw [← hdeq] at h2
    have h3 : ‖Zk k ω - Z ω‖ = ‖Z ω - Tn (nk k ω)‖ := by
      simp only [Zk]
      rw [norm_sub_rev]
    rw [h3, le_div_iff₀ (by positivity)]
    set x := ‖Z ω - Tn (nk k ω)‖ with hx
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have h4 : C * x * x < 1 / ((k : ℝ) + 1) := lt_of_le_of_lt h2 h1
    rw [lt_div_iff₀ hk1] at h4
    nlinarith [h4]
  have hlim : Tendsto (fun k : ℕ => 1 / (C * ((k : ℝ) + 1))) atTop (𝓝 0) := by
    have h0 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul C⁻¹
    rw [mul_zero] at h0
    refine h0.congr fun k => ?_
    field_simp
  have hsqrt : Tendsto (fun k : ℕ => Real.sqrt (1 / (C * ((k : ℝ) + 1)))) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hlim
    rw [Real.sqrt_zero] at this
    exact this
  refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hsqrt
  have := hsq k
  calc ‖Zk k ω - Z ω‖ = Real.sqrt (‖Zk k ω - Z ω‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (1 / (C * ((k : ℝ) + 1))) := Real.sqrt_le_sqrt this

theorem ofBlockVec_add (X Y : BlockVec 2) :
    HilbertBlockVec.ofBlockVec (X + Y) =
      HilbertBlockVec.ofBlockVec X + HilbertBlockVec.ofBlockVec Y := by
  apply WithLp.ofLp_injective
  funext i
  fin_cases i
  · simp [HilbertBlockVec.ofBlockVec, HilbertVec.ofVec, WithLp.toLp_add]
  · simp [HilbertBlockVec.ofBlockVec, HilbertVec.ofVec, WithLp.toLp_add]

theorem ofBlockVec_smul (c : ℝ) (X : BlockVec 2) :
    HilbertBlockVec.ofBlockVec (c • X) = c • HilbertBlockVec.ofBlockVec X := by
  apply WithLp.ofLp_injective
  funext i
  fin_cases i
  · simp [HilbertBlockVec.ofBlockVec, HilbertVec.ofVec, WithLp.toLp_smul]
  · simp [HilbertBlockVec.ofBlockVec, HilbertVec.ofVec, WithLp.toLp_smul]

theorem toH_add {U : Set (Vec 2)} {F G : Vec 2 → BlockVec 2} (hF : MemBlockL2 U F)
    (hG : MemBlockL2 U G) :
    toHilbertBlockL2OfBlockField (hF.add hG) =
      toHilbertBlockL2OfBlockField hF + toHilbertBlockL2OfBlockField hG := by
  apply Lp.ext
  filter_upwards [coeFn_toHilbertBlockL2OfBlockField (hF.add hG),
    coeFn_toHilbertBlockL2OfBlockField hF, coeFn_toHilbertBlockL2OfBlockField hG,
    Lp.coeFn_add (toHilbertBlockL2OfBlockField hF) (toHilbertBlockL2OfBlockField hG)]
    with x h1 h2 h3 h4
  rw [h1, h4]
  simp only [Pi.add_apply, h2, h3]
  simp [hilbertifyBlockField, ofBlockVec_add]

theorem toH_smul {U : Set (Vec 2)} {F : Vec 2 → BlockVec 2} (hF : MemBlockL2 U F) (c : ℝ) :
    toHilbertBlockL2OfBlockField (hF.const_smul c) = c • toHilbertBlockL2OfBlockField hF := by
  apply Lp.ext
  filter_upwards [coeFn_toHilbertBlockL2OfBlockField (hF.const_smul c),
    coeFn_toHilbertBlockL2OfBlockField hF,
    Lp.coeFn_smul c (toHilbertBlockL2OfBlockField hF)] with x h1 h2 h4
  rw [h1, h4]
  simp only [Pi.smul_apply, h2]
  simp [hilbertifyBlockField, ofBlockVec_smul]

/-- The `L²` classes of the genuine source variations form a linear subspace. -/
def variationSubmodule (Q : TriadicCube 2) : Submodule ℝ (HilbertBlockL2 (openCubeSet Q)) where
  carrier := {h | ∃ (Y : Vec 2 → BlockVec 2) (hY : ScalarVariation (openCubeSet Q) Y),
    h = toHilbertBlockL2OfBlockField hY.1}
  add_mem' := by
    rintro _ _ ⟨Y, hY, rfl⟩ ⟨Y', hY', rfl⟩
    exact ⟨Y + Y', scalar_variation_add hY hY', (toH_add hY.1 hY'.1).symm⟩
  zero_mem' := by
    refine ⟨(0 : ℝ) • (0 : Vec 2 → BlockVec 2),
      scalar_variation_smul (scalar_variation_zero (openCubeSet Q)) 0, ?_⟩
    have := toH_smul (scalar_variation_zero (openCubeSet Q)).1 0
    exact (zero_smul ℝ _).symm.trans this.symm
  smul_mem' := by
    rintro c _ ⟨Y, hY, rfl⟩
    exact ⟨c • Y, scalar_variation_smul hY c, (toH_smul hY.1 c).symm⟩

/-- The actual OLD maximizer, as an `L²` class, is a measurable function of the OLD sample. -/
theorem maximizer_class_measurable
    (M : ABKModel 2) (m : ℤ) (Q : TriadicCube 2) (w : Vec 2 → Vec 2)
    (hw : MemVectorL2 (openCubeSet Q) w)
    (Z : Cutoff.CutoffSample 2 → Vec 2 → BlockVec 2)
    (hZ : ∀ ω, IsScalarOldMaximizer Q M.nu (Annealed.sigmaBar M m : ℝ)
      (oldCutoffSkewCoefficient m Q ω) w (Z ω)) :
    Measurable fun ω => toHilbertBlockL2OfBlockField (hZ ω).1.1 := by
  classical
  letI finiteCell : IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  letI : IsSeparable (volumeMeasureOn (openCubeSet Q)) := inferInstance
  letI : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  letI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
  letI : SecondCountableTopology (HilbertBlockL2 (openCubeSet Q)) := inferInstance
  let hσ : 0 < (Annealed.sigmaBar M m : ℝ) := (Annealed.sigmaBar M m).property
  let B : Cutoff.CutoffSample 2 → HilbertBlockL2 (openCubeSet Q) →L[ℝ]
      HilbertBlockL2 (openCubeSet Q) →L[ℝ] ℝ := fun ω =>
    (scalarFrameRealization Q M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos hσ
      (oldCutoffSkewCoefficient m Q ω)).energyBilin
  have hB : Measurable B :=
    measurable_oldCutoff_scalarFrameEnergyBilin m Q M.nu (Annealed.sigmaBar M m : ℝ)
      M.nu_pos hσ
  have hev (T : HilbertBlockL2 (openCubeSet Q)) : Measurable fun ω => B ω T T :=
    (hB.clm_apply measurable_const).clm_apply measurable_const
  let ℓ := pairingCLM (openCubeSet Q) hw
  refine argmax_measurable B hB hev
    (fun ω x y => (scalarFrameRealization Q M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos hσ
      (oldCutoffSkewCoefficient m Q ω)).energySymm x y)
    (fun ω => (scalarFrameRealization Q M.nu (Annealed.sigmaBar M m : ℝ) M.nu_pos hσ
      (oldCutoffSkewCoefficient m Q ω)).energyCoercive)
    ℓ (variationSubmodule Q) _
    (fun ω => ⟨Z ω, (hZ ω).1, rfl⟩) ?_
  intro ω T hT
  obtain ⟨Y, hY, rfl⟩ := hT
  have h1 := (hZ ω).2 Y hY
  have e1 : ℓ (toHilbertBlockL2OfBlockField hY.1) =
      scalarSourcePairing (openCubeSet Q) w Y := pairingCLM_eq hw hY.1
  have e2 : B ω (toHilbertBlockL2OfBlockField hY.1) (toHilbertBlockL2OfBlockField hY.1) =
      scalarFieldEnergy M.nu (Annealed.sigmaBar M m : ℝ)
        (oldCutoffSkewCoefficient m Q ω) Y :=
    (scalar_field_energy_eq_bilin Q M.nu _ M.nu_pos hσ _ hY.1).symm
  have e3 : ℓ (toHilbertBlockL2OfBlockField (hZ ω).1.1) =
      scalarSourcePairing (openCubeSet Q) w (Z ω) := pairingCLM_eq hw _
  have e4 : B ω (toHilbertBlockL2OfBlockField (hZ ω).1.1)
      (toHilbertBlockL2OfBlockField (hZ ω).1.1) =
      scalarFieldEnergy M.nu (Annealed.sigmaBar M m : ℝ)
        (oldCutoffSkewCoefficient m Q ω) (Z ω) :=
    (scalar_field_energy_eq_bilin Q M.nu _ M.nu_pos hσ _ (hZ ω).1.1).symm
  rw [e1, e2, e3, e4]
  exact h1

end

end ASDExplicitGamma.Scalar
