module

public import ASDExplicitGamma.Gaussian.H3SeriesCompletion
public import ASDExplicitGamma.Gaussian.FiniteFactorLaw

/-! # Ordinary-H³ and actual C¹ factors for a finite q3 fresh band -/

@[expose] public section

open MeasureTheory Homogenization
open scoped Topology ENNReal

namespace ASDExplicitGamma.Gaussian

section
variable {n : ℕ} [NeZero n] (a b c d : ℝ) (β : Fin n → ℝ)
  (L : Fin n → {l : ℝ // 0 < l})

abbrev Q3BandH3 := PiLp 2 (fun i => Q3H3Range a b c d (β i) (L i))

noncomputable instance instQ3BandH3InnerProductSpace :
    @InnerProductSpace ℝ (Q3BandH3 a b c d β L) inferInstance
      (inferInstance : NormedAddCommGroup (Q3BandH3 a b c d β L)).toSeminormedAddCommGroup := by
  convert (@PiLp.innerProductSpace ℝ inferInstance (Fin n) inferInstance
    (fun i => Q3H3Range a b c d (β i) (L i)) (fun _ => inferInstance)
    (fun i => instQ3H3RangeInnerProductSpace a b c d (β i) (L i))) using 1

noncomputable instance instQ3BandH3NormedSpace :
    NormedSpace ℝ (Q3BandH3 a b c d β L) :=
  @PiLp.normedSpace 2 ℝ (Fin n) (fun i => Q3H3Range a b c d (β i) (L i))
    inferInstance inferInstance inferInstance (fun _ => inferInstance) (fun _ => inferInstance)

noncomputable def q3BandH3Directions : ℕ → Q3BandH3 a b c d β L :=
  finiteDirections (fun i => Q3H3Range a b c d (β i) (L i))
    (fun i => q3H3Directions a b c d (β i) (L i) whiteBasis)

/-- The direct-sum Hilbert directions are square summable in ordinary Sobolev norms. -/
theorem q3BandH3Directions_summable :
    Summable (fun j => ‖q3BandH3Directions a b c d β L j‖ ^ 2) :=
  finiteDirections_summable _ _ (fun i => q3H3Directions_summable a b c d (β i) (L i) whiteBasis)

end
end ASDExplicitGamma.Gaussian
