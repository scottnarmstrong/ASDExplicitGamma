module

public import ASDExplicitGamma.Inverse.StoppedQ3Control
public import ASDExplicitGamma.Inverse.StoppedPlanarHeight
public import ASDExplicitGamma.Inverse.StoppedFineBlockMap

/-! The stopped-height tail for the actual root-relative q3 fields. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open Homogenization MeasureTheory Algsuperdiff.Section3
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model
noncomputable section

/-- Every fine starting site in a translated root, mapped to its literal
buffered physical block. The centered triadic indexing includes negative sites. -/
def rootBlockStart (Q : TriadicCube 2) (h : ℕ) (i : RootStartingIndex h) : BlockSite :=
  fineBlockIndex (fun d => (3^h:ℤ)*Q.index d+(i d).val-((3^h:ℤ)-1)/2)

/-- The source actual q3 stopped height, with fine label Q.scale-h at each
deterministic separation and the full 3^(2h) translated root population. -/
def q3StoppedHeight (M : ABKModel 2) (Q : TriadicCube 2) (H0 : ℕ) (τ η : ℝ) :
    Cutoff.CutoffSample 2 → ℕ :=
  planarStoppedHeight H0 (fun h => q3PlanarMarks M (Q.scale-h) τ η) (rootBlockStart Q)

theorem q3_stopped_height_measurable (M : ABKModel 2) (Q : TriadicCube 2)
    (H0 : ℕ) (τ η : ℝ) : Measurable (q3StoppedHeight M Q H0 τ η) :=
  planar_stopped_height_measurable H0 _
    (fun h => q3_local_mark_measurable M (Q.scale-h) τ η)
    (fun h => q3_positive_mark_measurable M (Q.scale-h) τ η) _

theorem q3_stopped_height_ge (M : ABKModel 2) (Q : TriadicCube 2)
    (H0 : ℕ) (τ η : ℝ) (ω : Cutoff.CutoffSample 2) : H0 ≤ q3StoppedHeight M Q H0 τ η ω :=
  planar_stopped_height_ge H0 _ _ ω

/-- The exact source tail, proved from the model and protected ordinary native
past, with no cluster, mark-control or Gaussian-tail premise. -/
theorem q3_stopped_height_tail (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (Q : TriadicCube 2) (H0 : ℕ) (hH0 : 333 ≤ H0)
    (τ : ℝ) (hτ : 0 < τ) (t : WaveGateTuple) (q : ℝ)
    (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000)
    (hraw : (364*3^80:ℝ)*(3*(61/10:ℝ)/τ)^12 ≤ q)
    (hpast : ∀ k ≤ Q.scale-H0+40, nativeInductionState M h k)
    (k : ℕ) (hk : H0 ≤ k) :
    (Cutoff.cutoffSampleLaw M).toMeasure.real {ω | k < q3StoppedHeight M Q H0 τ (waveGateEta t) ω} ≤
      Real.exp (-heightExponent k/32) := by
  apply planar_stopped_height_tail _ H0 hH0 _ q hq0 hq _ _ k hk
  intro r hr
  apply q3_mark_control M h hM hg (Q.scale-r) τ hτ t q hraw
  intro u hu
  apply hpast u
  omega

/-- Every later separation of the actual q3 blocked fields succeeds almost
surely at and above the selected height. -/
theorem q3_stopped_height_ae_good (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (Q : TriadicCube 2) (H0 : ℕ) (hH0 : 333 ≤ H0)
    (τ : ℝ) (hτ : 0 < τ) (t : WaveGateTuple) (q : ℝ)
    (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000)
    (hraw : (364*3^80:ℝ)*(3*(61/10:ℝ)/τ)^12 ≤ q)
    (hpast : ∀ u ≤ Q.scale-H0+40, nativeInductionState M h u) :
    ∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure, ∀ k,
      q3StoppedHeight M Q H0 τ (waveGateEta t) ω ≤ k →
      ω ∉ separationFailure (q3PlanarMarks M (Q.scale-k) τ (waveGateEta t)) k (rootBlockStart Q k) := by
  apply planar_stopped_height_ae_good _ H0 hH0 _ q hq0 hq
  intro r hr
  apply q3_mark_control M h hM hg (Q.scale-r) τ hτ t q hraw
  intro u hu
  apply hpast u
  omega

end
end ASDExplicitGamma.Inverse
