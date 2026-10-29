module

public import ASDExplicitGamma.Triadic.PlanarNeumannBridge
public import ASDExplicitGamma.Native.OldSignedPartitionSeries
public import ASDExplicitGamma.Native.OldSignedPairedProjectionTrace

/-! The complete positive-Haar restriction used by the mixed source.
The same physical field is restricted to children; no cellwise replacement
or truncation of the positive norm enters the bound. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Triadic Native
noncomputable section

/-- A nonnegative complete series on each physical cell is summable whenever
its finite spatial average is summable. -/
theorem old_hessian_cell_series_summable (Q : TriadicCube 2) (depth : ℕ)
    (f : ℕ → TriadicCube 2 → ℝ)
    (hf : ∀ j U, U ∈ descendantsAtDepth Q depth → 0≤f j U)
    (hs : Summable (fun j => descendantsAverage Q depth (f j)))
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) :
    Summable (fun j => f j U) := by
  classical
  have hc : ((descendantsAtDepth Q depth).card : ℝ) ≠ 0 := by
    rw [descendantsAtDepth_card]
    positivity
  have hsum : Summable (fun j => ∑ R ∈ descendantsAtDepth Q depth,f j R) := by
    convert hs.mul_left ((descendantsAtDepth Q depth).card : ℝ) using 1
    funext j
    change _ = _*((((descendantsAtDepth Q depth).card : ℝ)⁻¹)*_)
    rw [←mul_assoc,mul_inv_cancel₀ hc,one_mul]
  exact hsum.of_nonneg_of_le (fun j => hf j U hU)
    (fun j => Finset.single_le_sum (fun R hR => hf j R hR) hU)

/-- The average of local positive-depth increment energies is precisely the
corresponding parent increment energy. This identity keeps every depth. -/
theorem old_hessian_child_increment_energy (Q : TriadicCube 2) (depth j : ℕ)
    {f : Vec 2 → ℝ} (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    descendantsAverage Q depth (fun U => energy U (cubeIncrement U (j+1) f)) =
      energy Q (cubeIncrement Q (depth+j+1) f) := by
  have he : descendantsAverage Q depth (fun U => energy U (cubeIncrement U (j+1) f)) =
      descendantsAverage Q depth (fun U => energy U (cubeProjection U (j+1) f)-
        energy U (cubeProjection U j f)) := by
    unfold descendantsAverage
    dsimp only
    congr 1
    apply Finset.sum_congr rfl
    intro U hU
    exact energy_increment_succ U j (memLp_on_descendant_of_memLp hU hf)
  rw [he,old_signed_descendants_average_sub,descendantsAverage_localProjection_eq,
    descendantsAverage_localProjection_eq,energy_increment_succ Q (depth+j) hf]
  rw [Nat.add_assoc]

/-- Every actual descendant inherits positive-Haar finiteness from the
parent. This qualitative fact is uniform in depth and does not multiply any
quantitative coarse-to-fine source coefficient. -/
theorem old_hessian_positive_descendant_summable (Q : TriadicCube 2) (depth : ℕ)
    {q : ℝ} (hq : 0<q) {f : Vec 2 → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hs : Summable (fun j : ℕ => q^(j+1)*energy Q (cubeIncrement Q (j+1) f)))
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q depth) :
    Summable (fun j : ℕ => q^(j+1)*energy U (cubeIncrement U (j+1) f)) := by
  have ht : Summable (fun j : ℕ => q^(j+1)*energy Q (cubeIncrement Q (depth+j+1) f)) := by
    have hh := ((summable_nat_add_iff depth).2 hs).mul_left ((q^depth)⁻¹)
    convert hh using 1
    funext j
    rw [show j+depth+1=depth+(j+1) by omega,
      show depth+j+1=depth+(j+1) by omega,pow_add]
    field_simp [pow_ne_zero depth hq.ne']
    simp only [pow_add,pow_succ]
    ring
  apply old_hessian_cell_series_summable Q depth
    (fun j R => q^(j+1)*energy R (cubeIncrement R (j+1) f))
    (fun j R _ => mul_nonneg (pow_nonneg hq.le _) (energy_nonneg R _)) _ U hU
  convert ht using 1
  funext j
  rw [Homogenization.descendantsAverage_mul_left,old_hessian_child_increment_energy Q depth j hf]

/-- Genuine finite positive parent energy gives finite positive energy on
every child, before the real-valued complete norms are used. -/
theorem old_hessian_positive_child_summable (Q : TriadicCube 2) {q : ℝ} (hq : 0<q)
    {f : Vec 2 → ℝ} (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hs : Summable (fun j : ℕ => q^(j+1)*energy Q (cubeIncrement Q (j+1) f)))
    (U : TriadicCube 2) (hU : U ∈ descendantsAtDepth Q 1) :
    Summable (fun j : ℕ => q^(j+1)*energy U (cubeIncrement U (j+1) f)) := by
  have hq0 : 0<q := hq
  have ht : Summable (fun j : ℕ => q^(j+1)*energy Q (cubeIncrement Q (1+j+1) f)) := by
    have hh := ((summable_nat_add_iff 1).2 hs).mul_left q⁻¹
    convert hh using 1
    funext j
    rw [Nat.add_comm j 1,pow_succ q (1+j)]
    field_simp
  apply old_hessian_cell_series_summable Q 1
    (fun j R => q^(j+1)*energy R (cubeIncrement R (j+1) f))
    (fun j R _ => mul_nonneg (pow_nonneg hq0.le _) (energy_nonneg R _)) _ U hU
  convert ht using 1
  funext j
  rw [Homogenization.descendantsAverage_mul_left,old_hessian_child_increment_energy Q 1 j hf]

/-- Exact complete parent/child positive-energy identity for every positive
weight. Its reciprocal-weight specialization is the cell-zero weak shift. -/
theorem old_hessian_primal_child_identity (Q : TriadicCube 2) {q : ℝ} (hq : 0<q)
    {f : Vec 2 → ℝ} (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hs : Summable (fun j : ℕ => q^(j+1)*energy Q (cubeIncrement Q (j+1) f))) :
    primalEnergy Q q f = q*descendantsAverage Q 1 (fun U => primalEnergy U q f)+
      (1-q)*energy Q (cubeProjection Q 0 f) := by
  let tail := ∑' j : ℕ,q^(j+1)*energy Q (cubeIncrement Q (1+j+1) f)
  have hlocal := old_hessian_positive_child_summable Q hq hf hs
  have hpart := old_signed_partition_series Q 1
    (fun j U => q^(j+1)*energy U (cubeIncrement U (j+1) f)) hlocal
  have havg : descendantsAverage Q 1 (fun U => primalEnergy U q f) =
      energy Q (cubeProjection Q 1 f)+tail := by
    unfold primalEnergy
    rw [descendantsAverage_add]
    congr 1
    · simp only [cubeIncrement_zero]
      simpa only [Nat.add_zero] using descendantsAverage_localProjection_eq Q 1 0 f
    · rw [←hpart.2]
      apply tsum_congr
      intro j
      rw [Homogenization.descendantsAverage_mul_left,old_hessian_child_increment_energy Q 1 j hf]
  have hparent : primalEnergy Q q f = energy Q (cubeProjection Q 0 f)+
      q*energy Q (cubeIncrement Q 1 f)+q*tail := by
    unfold primalEnergy
    rw [cubeIncrement_zero,hs.tsum_eq_zero_add]
    simp only [zero_add,pow_one]
    rw [add_assoc]
    congr 1
    rw [←tsum_mul_left]
    congr 1
    apply tsum_congr
    intro j
    rw [Nat.add_comm j 1,pow_succ]
    ring
  have he := energy_increment_succ Q 0 hf
  simp only [zero_add] at he
  rw [havg,hparent]
  linarith only [congrArg (fun x : ℝ => q*x) he]

/-- Restricting a complete positive Haar norm to the nine children is
contractive, including the root means. Finiteness on all children is a
conclusion of the preceding lemma, not an omitted real-tsum premise. -/
theorem old_hessian_positive_child_restriction (Q : TriadicCube 2) {q : ℝ} (hq : 1≤q)
    {f : Vec 2 → ℝ} (hf : MemLp f 2 (normalizedCubeMeasure Q))
    (hs : Summable (fun j : ℕ => q^(j+1)*energy Q (cubeIncrement Q (j+1) f))) :
    descendantsAverage Q 1 (fun U => primalEnergy U q f) ≤ primalEnergy Q q f := by
  let tail := ∑' j : ℕ,q^(j+1)*energy Q (cubeIncrement Q (1+j+1) f)
  have ht : 0≤tail := tsum_nonneg (fun j => mul_nonneg
    (pow_nonneg (zero_le_one.trans hq) _) (energy_nonneg Q _))
  have hlocal := old_hessian_positive_child_summable Q (zero_lt_one.trans_le hq) hf hs
  have hpart := old_signed_partition_series Q 1
    (fun j U => q^(j+1)*energy U (cubeIncrement U (j+1) f)) hlocal
  have havg : descendantsAverage Q 1 (fun U => primalEnergy U q f) =
      energy Q (cubeProjection Q 1 f)+tail := by
    unfold primalEnergy
    rw [descendantsAverage_add]
    congr 1
    · simp only [cubeIncrement_zero]
      simpa only [Nat.add_zero] using descendantsAverage_localProjection_eq Q 1 0 f
    · rw [←hpart.2]
      apply tsum_congr
      intro j
      rw [Homogenization.descendantsAverage_mul_left,old_hessian_child_increment_energy Q 1 j hf]
  have hparent : primalEnergy Q q f = energy Q (cubeProjection Q 0 f)+
      q*energy Q (cubeIncrement Q 1 f)+q*tail := by
    unfold primalEnergy
    rw [cubeIncrement_zero,hs.tsum_eq_zero_add]
    simp only [zero_add,pow_one]
    rw [add_assoc]
    congr 1
    rw [←tsum_mul_left]
    congr 1
    apply tsum_congr
    intro j
    rw [Nat.add_comm j 1,pow_succ]
    ring
  have he := energy_increment_succ Q 0 hf
  simp only [zero_add] at he
  have hinc : energy Q (cubeProjection Q 1 f)=
      energy Q (cubeProjection Q 0 f)+energy Q (cubeIncrement Q 1 f) := by
    linarith only [he]
  rw [havg,hparent,hinc]
  have h1 := mul_le_mul_of_nonneg_right hq (energy_nonneg Q (cubeIncrement Q 1 f))
  have h2 := mul_le_mul_of_nonneg_right hq ht
  simp only [one_mul] at h1 h2
  linarith only [h1,h2]

/-- The actual coordinate-summed positive norm has the same contractive
restriction; there is no factor from the number of vector coordinates. -/
theorem old_hessian_vector_positive_child_restriction {m : ℕ}
    (Q : TriadicCube 2) (F : Vec 2 → Fin m → ℝ)
    (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (hs : ∀ i, Summable (fun j : ℕ => (Real.sqrt 3)^(j+1)*
      energy Q (cubeIncrement Q (j+1) (fun x => F x i)))) :
    descendantsAverage Q 1 (fun U => vectorPositiveHaarEnergy U F) ≤
      vectorPositiveHaarEnergy Q F := by
  have hq : (1:ℝ)≤Real.sqrt 3 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (by norm_num : (1:ℝ)≤3)
  unfold vectorPositiveHaarEnergy
  rw [Homogenization.descendantsAverage_sum]
  exact Finset.sum_le_sum (fun i _ => old_hessian_positive_child_restriction Q hq (hF i) (hs i))

end
end ASDExplicitGamma.Scalar
