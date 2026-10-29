module

public import ASDExplicitGamma.Gaussian.DerivativeLawAugment
public import ASDExplicitGamma.Model.ShellScaling

/-! Joint Gaussian law of the literal frozen C2 shell observations. -/

@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Homogenization Algsuperdiff.Frozen.Assumptions MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.Elementwise
noncomputable section

/-- Value, first, or second directional observation of the stored scalar stream. -/
inductive ShellDerivativeObservation where
  | value (x : Vec 2)
  | first (x v : Vec 2)
  | second (x v w : Vec 2)

/-- The literal scalar (1,0) entry projection. -/
def shellScalarEntry : Mat 2 →L[ℝ] ℝ where
  toFun A := A 1 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by fun_prop

 def shellScalarValue (j : ShellField 2) (x : Vec 2) : ℝ := shellScalarEntry (j x)
 def shellScalarDerivative (j : ShellField 2) (x : Vec 2) : Vec 2 →L[ℝ] ℝ :=
  shellScalarEntry.comp (j.deriv x)
 def shellScalarFirst (v : Vec 2) (j : ShellField 2) (x : Vec 2) : ℝ := shellScalarDerivative j x v
 def shellScalarFirstDerivative (v : Vec 2) (j : ShellField 2) (x : Vec 2) : Vec 2 →L[ℝ] ℝ :=
  (shellScalarEntry.comp (ContinuousLinearMap.apply ℝ (Mat 2) v)).comp (j.secondDeriv x)

/-- Evaluation uses the stored, actual derivatives, rather than arbitrary derivative witnesses. -/
def shellDerivativeEval : ShellDerivativeObservation → ShellField 2 → ℝ
  | .value x, j => shellScalarValue j x
  | .first x v, j => shellScalarFirst v j x
  | .second x v w, j => shellScalarFirstDerivative v j x w

 theorem shellScalarValue_hasFDerivAt (j : ShellField 2) (x : Vec 2) :
    HasFDerivAt (shellScalarValue j) (shellScalarDerivative j x) x := by
  simpa only [shellScalarValue, shellScalarDerivative, Function.comp_def] using!
    shellScalarEntry.hasFDerivAt.comp x (j.hasFDerivAt x)

 theorem shellScalarFirst_hasFDerivAt (v : Vec 2) (j : ShellField 2) (x : Vec 2) :
    HasFDerivAt (shellScalarFirst v j) (shellScalarFirstDerivative v j x) x := by
  simpa only [shellScalarFirst, shellScalarDerivative, shellScalarFirstDerivative,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, Function.comp_def] using!
    (shellScalarEntry.comp (ContinuousLinearMap.apply ℝ (Mat 2) v)).hasFDerivAt.comp x (j.deriv_hasFDerivAt x)

 theorem shellDerivativeEval_continuous (o : ShellDerivativeObservation) : Continuous (shellDerivativeEval o) := by
  cases o with
  | value x => exact shellScalarEntry.continuous.comp (ShellField.continuous_eval x)
  | first x v =>
      exact (shellScalarEntry.comp (ContinuousLinearMap.apply ℝ (Mat 2) v)).continuous.comp (ShellField.continuous_eval_deriv x)
  | second x v w =>
      exact ((shellScalarEntry.comp (ContinuousLinearMap.apply ℝ (Mat 2) v)).comp (ContinuousLinearMap.apply ℝ (Vec 2 →L[ℝ] Mat 2) w)).continuous.comp (ShellField.continuous_eval_secondDeriv x)

/-- Any genuinely Gaussian value law on the frozen C2 carrier has the complete
joint Gaussian law of all stored values and first/second derivatives. -/
theorem isCenteredGaussianFamily_stored_derivatives (μ : Measure (ShellField 2)) [IsProbabilityMeasure μ]
    (hvalue : IsCenteredGaussianFamily μ (fun x j => shellScalarValue j x)) :
    IsCenteredGaussianFamily μ shellDerivativeEval := by
  let f : Unit → ShellField 2 → Vec 2 → ℝ := fun _ => shellScalarValue
  let D : Unit → ShellField 2 → Vec 2 → Vec 2 →L[ℝ] ℝ := fun _ => shellScalarDerivative
  have hbase : IsCenteredGaussianFamily μ (fun p : Unit × Vec 2 => fun j => f p.1 j p.2) := hvalue.comp Prod.snd
  have haug := isCenteredGaussianFamily_derivativeAugment μ f D hbase
    (fun _ x v => (shellDerivativeEval_continuous (.first x v)).measurable.aemeasurable)
    (fun _ j x => shellScalarValue_hasFDerivAt j x)
  let g : Option (Vec 2) → ShellField 2 → Vec 2 → ℝ :=
    fun a => a.elim shellScalarValue (fun v => shellScalarFirst v)
  let G : Option (Vec 2) → ShellField 2 → Vec 2 → Vec 2 →L[ℝ] ℝ :=
    fun a => a.elim shellScalarDerivative (fun v => shellScalarFirstDerivative v)
  have hg : IsCenteredGaussianFamily μ (fun p : Option (Vec 2) × Vec 2 => fun j => g p.1 j p.2) := by
    let map : Option (Vec 2) × Vec 2 → Sum (Unit × Vec 2) ((Unit × Vec 2) × Vec 2) :=
      fun p => p.1.elim (Sum.inl ((),p.2)) (fun v => Sum.inr (((),p.2),v))
    have heq : (fun p : Option (Vec 2) × Vec 2 => fun j => g p.1 j p.2) = (fun p => derivativeAugment f D (map p)) := by
      funext p j
      rcases p with ⟨a,x⟩
      cases a <;> rfl
    rw [heq]
    exact haug.comp map
  have hG : ∀ a x v, AEMeasurable (fun j => G a j x v) μ := by
    intro a x v
    cases a with
    | none => exact (shellDerivativeEval_continuous (.first x v)).measurable.aemeasurable
    | some w => exact (shellDerivativeEval_continuous (.second x w v)).measurable.aemeasurable
  have hgd : ∀ a j x, HasFDerivAt (g a j) (G a j x) x := by
    intro a j x
    cases a with
    | none => exact shellScalarValue_hasFDerivAt j x
    | some v => exact shellScalarFirst_hasFDerivAt v j x
  have haug2 := isCenteredGaussianFamily_derivativeAugment μ g G hg hG hgd
  let map : ShellDerivativeObservation → Sum (Option (Vec 2) × Vec 2) ((Option (Vec 2) × Vec 2) × Vec 2) := fun o => match o with
    | .value x => Sum.inl (none,x)
    | .first x v => Sum.inl (some v,x)
    | .second x v w => Sum.inr ((some v,x),w)
  have heq : (fun o => derivativeAugment g G (map o)) = shellDerivativeEval := by
    funext o j
    cases o <;> rfl
  rw [← heq]
  exact haug2.comp map

end
end ASDExplicitGamma.Gaussian
