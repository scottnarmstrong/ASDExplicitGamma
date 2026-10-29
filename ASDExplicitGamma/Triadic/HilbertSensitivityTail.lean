module

public import ASDExplicitGamma.Triadic.HilbertHaarParseval
public import ASDExplicitGamma.Triadic.HaarWeightedTail

/-! Exact source positive-norm tail identities, including genuine summability. -/

@[expose] public section
namespace ASDExplicitGamma.Triadic
open Homogenization MeasureTheory
open scoped BigOperators
noncomputable section

 theorem hilbertEnergy_nonneg {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (Q : TriadicCube d) (F : Vec d → E) : 0 ≤ hilbertEnergy Q F := integral_nonneg fun _ => sq_nonneg _

/-- Positive Haar membership proves residual-tail summability and both Abel identities.
No convergence or tail-identity premise is added to the source L2 and P membership. -/
theorem hilbert_sensitivity_tail_of_weight {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (Q : TriadicCube d) {q : ℝ} (hq : 1 < q)
    {F : Vec d → E} (hF : MemLp F 2 (normalizedCubeMeasure Q))
    (hs : Summable (fun k => q^(k+1)*hilbertEnergy Q (hilbertCubeIncrement Q (k+1) F))) :
    Summable (fun j => q^j*hilbertEnergy Q (fun x => F x-hilbertCubeProjection Q j F x)) ∧
    hilbertPrimalEnergy Q q F = hilbertEnergy Q F+(q-1)*
      ∑' j, q^j*hilbertEnergy Q (fun x => F x-hilbertCubeProjection Q j F x) ∧
    hilbertPrimalCircEnergy Q q F = hilbertEnergy Q (fun x => F x-hilbertCubeProjection Q 0 F x)+(q-1)*
      ∑' j, q^j*hilbertEnergy Q (fun x => F x-hilbertCubeProjection Q j F x) := by
  let a : ℕ → ℝ := fun n => hilbertEnergy Q (hilbertCubeIncrement Q n F)
  have ha (n : ℕ) : 0 ≤ a n := hilbertEnergy_nonneg Q _
  have hw : Summable (fun n => q^n*a n) := (summable_nat_add_iff 1).1 hs
  have hr (j : ℕ) : hilbertEnergy Q (fun x => F x-hilbertCubeProjection Q j F x) = haarEnergyTail a j :=
    (hilbert_haar_parseval Q hF).2.2 j
  have hp : hilbertPrimalEnergy Q q F = ∑' n, q^n*a n := by
    simpa only [hilbertPrimalEnergy, pow_zero, one_mul] using hw.tsum_eq_zero_add.symm
  have hid := haarEnergyTail_identity ha hq hw
  have hsum : (∑' n, a n) = hilbertEnergy Q F := (hilbert_haar_parseval Q hF).2.1
  rw [hsum] at hid
  have hfull : hilbertPrimalEnergy Q q F = hilbertEnergy Q F+(q-1)*∑' j, q^j*haarEnergyTail a j := by
    rw [hp]; exact hid
  have haa := summable_of_summable_weighted_energy ha hq hw
  have hu := haa.tsum_eq_zero_add
  change (∑' n, a n) = a 0+haarEnergyTail a 0 at hu
  rw [hsum] at hu
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hr] using haarEnergyTail_weighted_summable ha hq hw
  · simpa only [hr] using hfull
  · simp_rw [hr]
    change hilbertEnergy Q (hilbertCubeIncrement Q 0 F)+hilbertPrimalCircEnergy Q q F = _ at hfull
    change hilbertEnergy Q F = hilbertEnergy Q (hilbertCubeIncrement Q 0 F)+haarEnergyTail a 0 at hu
    linarith only [hfull, hu]

/-- TR-SENSITIVITY-TAIL, for the source weight 3^(2s), on every real Hilbert space. -/
theorem hilbert_sensitivity_tail {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (Q : TriadicCube d) (s : ℝ) (hs : 0 < s ∧ s < 1)
    {F : Vec d → E} (hF : MemLp F 2 (normalizedCubeMeasure Q))
    (hP : Summable (fun k => ((3:ℝ)^(2*s))^(k+1)*hilbertEnergy Q (hilbertCubeIncrement Q (k+1) F))) :
    let q := (3:ℝ)^(2*s)
    Summable (fun j => q^j*hilbertEnergy Q (fun x => F x-hilbertCubeProjection Q j F x)) ∧
    hilbertPrimalEnergy Q q F = hilbertEnergy Q F+(q-1)*
      ∑' j, q^j*hilbertEnergy Q (fun x => F x-hilbertCubeProjection Q j F x) ∧
    hilbertPrimalCircEnergy Q q F = hilbertEnergy Q (fun x => F x-hilbertCubeProjection Q 0 F x)+(q-1)*
      ∑' j, q^j*hilbertEnergy Q (fun x => F x-hilbertCubeProjection Q j F x) := by
  exact hilbert_sensitivity_tail_of_weight Q (Real.one_lt_rpow (by norm_num) (mul_pos (by norm_num) hs.1)) hF hP

end
end ASDExplicitGamma.Triadic
