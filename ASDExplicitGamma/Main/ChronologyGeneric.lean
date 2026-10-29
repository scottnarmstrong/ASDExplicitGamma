module

public import ASDExplicitGamma.Main.ChronologyList
public import ASDExplicitGamma.Main.ChronologyCompose

/-! Chronology: the generic 40-insertion induction against `mainCert`. For any
per-insertion step hypothesis with a factor `c` (`c = 1` for MA-CHRONOLOGY at `γ₀`, `c = θ` for the
θ-continuation), the cold lag-40 input composes to `c · composeUpper mainCert / G`. -/

@[expose] public section

namespace ASDExplicitGamma.Main

open ASDExplicitGamma.Numerics ASDExplicitGamma.Numerics.MainReturnCertificate
open ASDExplicitGamma.Numerics.Spike
open MeasureTheory Homogenization Algsuperdiff.Section3

theorem main_composed_generic_prefix (M : ABKModel 2) (m : ℤ) (c : ℝ)
    (C : List InsertionCert)
    (hcold : (∫ ω, cutoffTraceDefect M m (m + 40) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      c * ((Spike.cold40Upper : ℝ) / (Spike.gridScale : ℝ)))
    (hstep : ∀ i : ℕ, i < 40 → ∀ (cert : InsertionCert) (x0 : ℕ), C[i]? = some cert →
      (∫ ω, cutoffTraceDefect M (m + (i : ℤ)) (m + 40) ω
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ c * ((x0 : ℝ) / (Spike.gridScale : ℝ)) →
      (∫ ω, cutoffTraceDefect M (m + (i : ℤ) + 1) (m + 40) ω
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        c * ((advanceInsertion x0 cert : ℝ) / (Spike.gridScale : ℝ)))
    (hC : ∀ i : ℕ, i < 40 → ∃ cert, C[i]? = some cert) :
    ∀ i : ℕ, i ≤ 40 →
      (∫ ω, cutoffTraceDefect M (m + (i : ℤ)) (m + 40) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        c * ((((C.take i).foldl advanceInsertion Spike.cold40Upper : ℕ) : ℝ) /
          (Spike.gridScale : ℝ)) := by
  intro i
  induction i with
  | zero => intro _; simpa using hcold
  | succ i ih =>
    intro hi
    have hi40 : i < 40 := by omega
    obtain ⟨cert, hcert⟩ := hC i hi40
    have hstep' := hstep i hi40 cert _ hcert (ih (by omega))
    have hidx' : m + ((i + 1 : ℕ) : ℤ) = m + (i : ℤ) + 1 := by push_cast; ring
    rw [hidx', foldl_take_succ advanceInsertion Spike.cold40Upper C i _ hcert]
    exact hstep'

/-- Generic composition against `mainCert`. -/
theorem main_composed_generic (M : ABKModel 2) (m : ℤ) (c : ℝ)
    (hcold : (∫ ω, cutoffTraceDefect M m (m + 40) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      c * ((Spike.cold40Upper : ℝ) / (Spike.gridScale : ℝ)))
    (hstep : ∀ i : ℕ, i < 40 → ∀ (cert : InsertionCert) (x0 : ℕ), mainCert[i]? = some cert →
      (∫ ω, cutoffTraceDefect M (m + (i : ℤ)) (m + 40) ω
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤ c * ((x0 : ℝ) / (Spike.gridScale : ℝ)) →
      (∫ ω, cutoffTraceDefect M (m + (i : ℤ) + 1) (m + 40) ω
        ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
        c * ((advanceInsertion x0 cert : ℝ) / (Spike.gridScale : ℝ))) :
    (∫ ω, cutoffTraceDefect M (m + 40) (m + 40) ω ∂(Cutoff.cutoffSampleLaw M).toMeasure) ≤
      c * ((Spike.composeUpper mainCert : ℝ) / (Spike.gridScale : ℝ)) := by
  have h := main_composed_generic_prefix M m c mainCert hcold hstep
    (fun i hi => by
      obtain ⟨ins, _, hg⟩ := mainCert_get i hi
      exact ⟨_, hg⟩) 40 le_rfl
  rw [List.take_of_length_le (by rw [mainCert_length])] at h
  exact_mod_cast h

end ASDExplicitGamma.Main

end
