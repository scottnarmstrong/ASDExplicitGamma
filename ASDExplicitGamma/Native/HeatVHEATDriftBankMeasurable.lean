module

public import ASDExplicitGamma.Native.HeatVHEATDriftBankIdentity

/-! Genuine measurability of the actual refined drift-bank integrands. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Response Scalar Variational Gaussian Inverse Triadic Algsuperdiff.Section3
open scoped ENNReal
noncomputable section

/-- The actual source bank is a measurable complete physical history,
without imposing a bank estimate or regularity hypothesis. -/
theorem heatVHEATDrift_bank_measurable
    (M : ABKModel 2) (n : ℤ) (height : ℕ) (t : ℝ) (d : Fin 9) :
    Measurable (fun ω => heatVHEATDriftBank M n height t ω 0 d) := by
  classical
  let s := descendantsAtDepth (originCube 2 (n-1)) (pureFluxBankSourceDepth (d.val+2))
  let f := fun U ω => (bankRootInverseHistory U M n (n+(height:ℤ)) (fun _ => Real.sqrt t) ω).toReal
  let H := historyFiniteMax (Finset.univ : Finset ↥s) (fun U ω => ENNReal.ofReal (f U.1 ω))
  have hm : Measurable H := history_finite_max_measurable _ _ (fun U =>
    ENNReal.continuous_ofReal.measurable.comp
      (bank_root_inverse_history_measurable U.1 M n (n+(height:ℤ)) (fun _ => Real.sqrt t)).ennreal_toReal)
  have heq : (fun ω => heatVHEATDriftBank M n height t ω 0 d)=(fun ω => (H ω).toReal) := by
    funext ω
    rw [heatVHEATDrift_bank_eq_root_max]
    have hh := bank_finite_max_ofReal s (descendantsAtDepth_nonempty _ _) (fun U => f U ω)
    have hH : H ω=ENNReal.ofReal (Book.Ch02.finsetSupReal s (fun U => f U ω)) := hh
    rw [hH,ENNReal.toReal_ofReal (Book.Ch02.finsetSupReal_nonneg _ _ (fun _ _ => ENNReal.toReal_nonneg))]
  rw [heq]
  exact hm.ennreal_toReal

/-- Arbitrary jointly coupled auxiliary gauges do not affect the actual
bank's measurability; the bank is physical and gauge-invariant pointwise. -/
theorem heatVHEATDrift_translated_bank_measurable
    (M : ABKModel 2) (n : ℤ) (height : ℕ) (t : ℝ) (shift : Vec 2)
    (g : (ℕ → ℝ) → ℝ) (d : Fin 9) :
    Measurable (fun z : Cutoff.CutoffSample 2 × (ℕ → ℝ) =>
      heatVHEATDriftBank M n height t (Cutoff.translateCutoffSample shift z.1) (g z.2) d) := by
  have heq : (fun z : Cutoff.CutoffSample 2 × (ℕ → ℝ) =>
      heatVHEATDriftBank M n height t (Cutoff.translateCutoffSample shift z.1) (g z.2) d)=
      (fun z : Cutoff.CutoffSample 2 × (ℕ → ℝ) =>
        heatVHEATDriftBank M n height t (Cutoff.translateCutoffSample shift z.1) 0 d) :=
    funext (fun z => heatVHEATDrift_bank_gauge M n height t _ _ d)
  rw [heq]
  exact (heatVHEATDrift_bank_measurable M n height t d).comp
    ((Cutoff.measurable_translateCutoffSample shift).comp measurable_fst)

end
end ASDExplicitGamma.Native
