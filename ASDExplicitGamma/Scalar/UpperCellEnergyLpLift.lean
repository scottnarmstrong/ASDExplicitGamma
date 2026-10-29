module

public import ASDExplicitGamma.Scalar.UpperCellEnergyLpMeasurability

/-! A measurable L² lift agrees with every finite spatial section. Null
exceptional sections receive zero; no estimate or finiteness is assumed there. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open MeasureTheory
noncomputable section

/-- The L² seminorm of a jointly measurable field is a measurable extended
real random variable, including on sections of infinite norm. -/
theorem upper_cell_section_norm_measurable
    {Ω X E : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (μ : Measure X) [SFinite μ]
    (F : Ω → X → E) (hF : Measurable (Function.uncurry F)) :
    Measurable (fun ω => eLpNorm (F ω) 2 μ) := by
  have hm := (hF.enorm.pow_const (2:ℝ)).lintegral_prod_right' (ν := μ)
  have hr := hm.pow_const (1/(2:ℝ))
  convert hr using 1
  funext ω
  simpa only [ENNReal.toReal_ofNat, Function.uncurry] using
    (eLpNorm_eq_lintegral_rpow_enorm_toReal (p := (2:ENNReal))
      (by norm_num) (by norm_num) (hF.of_uncurry_left.aestronglyMeasurable (μ := μ)))

/-- A jointly measurable field has a measurable L²-valued lift that agrees
with every L² section. In applications the good sections have full measure. -/
theorem upper_cell_measurable_Lp_lift
    {Ω X E : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (μ : Measure X) [SFinite μ]
    [MeasurableSpace (Lp E 2 μ)] [BorelSpace (Lp E 2 μ)]
    [SecondCountableTopology (Lp E 2 μ)]
    (F : Ω → X → E) (hF : Measurable (Function.uncurry F)) :
    ∃ G : Ω → Lp E 2 μ, Measurable G ∧
      ∀ ω (hω : MemLp (F ω) 2 μ), G ω = hω.toLp (F ω) := by
  classical
  have hgood : MeasurableSet {ω | MemLp (F ω) 2 μ} := by
    have heq : {ω | MemLp (F ω) 2 μ} = {ω | eLpNorm (F ω) 2 μ < ⊤} := by
      ext ω
      rfl
    rw [heq]
    exact measurableSet_lt (upper_cell_section_norm_measurable μ F hF) measurable_const
  let F' : Ω → X → E := fun ω x => if MemLp (F ω) 2 μ then F ω x else 0
  have hm : Measurable (Function.uncurry F') :=
    Measurable.ite (hgood.preimage measurable_fst) hF measurable_const
  have hmem (ω : Ω) : MemLp (F' ω) 2 μ := by
    by_cases hω : MemLp (F ω) 2 μ
    · simpa only [F',ite_eq_left hω] using hω
    · simpa only [F',ite_eq_right hω, Pi.zero_def] using (MemLp.zero : MemLp (fun _ : X => (0:E)) 2 μ)
  refine ⟨fun ω => (hmem ω).toLp (F' ω), upper_cell_toLp_measurable μ F' hm hmem, ?_⟩
  intro ω hω
  apply Lp.ext
  exact ((hmem ω).coeFn_toLp).trans (by
    simpa only [F',ite_eq_left hω] using hω.coeFn_toLp.symm)

end
end ASDExplicitGamma.Scalar
