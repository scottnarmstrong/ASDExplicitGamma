module

public import ASDExplicitGamma.Triadic.KPRiesz
public import ASDExplicitGamma.Triadic.PlanarConstants
public import ASDExplicitGamma.Scalar.InverseHistory

/-! Constant-one Haar pairing at the source exponent 1/8. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar
open Homogenization MeasureTheory Triadic

/-- The exact square-weight base for source exponent 1/8. -/
noncomputable def sourceHaarBase : ℝ := (3:ℝ)^(1/4:ℝ)

/-- The source base exceeds one. -/
theorem source_haar_base_gt_one : 1 < sourceHaarBase :=
  Real.one_lt_rpow (by norm_num) (by norm_num)

/-- The positive source energy retains the root mean and both vector components. -/
noncomputable def positiveSourceEnergy (Q : TriadicCube 2) (f : Vec 2 → Vec 2) : ℝ :=
  ∑ i,primalEnergy Q sourceHaarBase (fun x => f x i)

/-- Positive Haar energies are nonnegative, independently of summability. -/
theorem primal_energy_nonneg (Q : TriadicCube 2) {q : ℝ} (hq : 0 ≤ q) (f : Vec 2 → ℝ) :
    0 ≤ primalEnergy Q q f :=
  add_nonneg (energy_nonneg Q _) (tsum_nonneg (fun j => mul_nonneg (pow_nonneg hq _) (energy_nonneg Q _)))

/-- Weak energies are nonnegative for the source base. -/
theorem dual_energy_nonneg (Q : TriadicCube 2) (f : Vec 2 → ℝ) :
    0 ≤ dualEnergy Q sourceHaarBase f := by
  exact primal_energy_nonneg Q (inv_nonneg.mpr (le_trans zero_le_one source_haar_base_gt_one.le)) f

/-- The pairing limit needed by constant-one duality follows from genuine L2 convergence. -/
theorem haar_pairing_projection_limit (Q : TriadicCube 2) {f g : Vec 2 → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) (hg : MemLp g 2 (normalizedCubeMeasure Q)) :
    Filter.Tendsto (fun N => pairing Q (cubeProjection Q N f) (cubeProjection Q N g))
      Filter.atTop (nhds (pairing Q f g)) := by
  have hc : Homogenization.cubeBesovConjExponent (2 : ENNReal)=2 := by
    simpa [Homogenization.cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq (p := (2:ENNReal)) (q := (2:ENNReal)))
  have ht : Homogenization.cubeBesovConjExponent (2:ENNReal)≠⊤ := by rw [hc];norm_num
  have h := Homogenization.tendsto_cubeBesovPairing_projection_left_of_memLp
    Q (2:ENNReal) f g hf (by simpa only [hc] using hg) (by norm_num) (by norm_num) ht
  have he (n : ℕ) : pairing Q (cubeProjection Q (n+1) f) (cubeProjection Q (n+1) g)=
      pairing Q (cubeProjection Q (n+1) f) g := by
    rw [pairing_projections Q (n+1) (n+1) hf hg, Nat.min_self]
    exact (projection_selfAdjoint Q (n+1) hf hg).symm
  apply (Filter.tendsto_add_atTop_iff_nat 1).1
  have h' : Filter.Tendsto (fun n => pairing Q (cubeProjection Q (n+1) f) g)
      Filter.atTop (nhds (pairing Q f g)) := by
    simpa only [Homogenization.cubeBesovPairing,pairing] using h
  exact Filter.Tendsto.congr' (Filter.Eventually.of_forall (fun n => (he n).symm)) h'

/-- Vector weak/positive duality has constant one and no assumed limiting pairing. -/
theorem vector_haar_pairing_bound (Q : TriadicCube 2) (r f : Vec 2 → Vec 2)
    (hr : ∀ i,MemLp (fun x => r x i) 2 (normalizedCubeMeasure Q))
    (hf : ∀ i,MemLp (fun x => f x i) 2 (normalizedCubeMeasure Q))
    (hs : ∀ i,Summable (fun j => sourceHaarBase^(j+1)*energy Q (cubeIncrement Q (j+1) (fun x => f x i)))) :
    |∑ i,pairing Q (fun x => r x i) (fun x => f x i)| ≤
      Real.sqrt (∑ i,dualEnergy Q sourceHaarBase (fun x => r x i))*Real.sqrt (positiveSourceEnergy Q f) := by
  calc
    _ ≤ ∑ i,|pairing Q (fun x => r x i) (fun x => f x i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i,Real.sqrt (dualEnergy Q sourceHaarBase (fun x => r x i))*
        Real.sqrt (primalEnergy Q sourceHaarBase (fun x => f x i)) := by
      apply Finset.sum_le_sum
      intro i _
      exact weak_positive_duality_of_weight Q source_haar_base_gt_one (hr i) (hf i) (hs i)
        (haar_pairing_projection_limit Q (hr i) (hf i))
    _ ≤ _ := Real.sum_sqrt_mul_sqrt_le Finset.univ
      (fun i => dual_energy_nonneg Q (fun x => r x i))
      (fun i => primal_energy_nonneg Q (le_trans zero_le_one source_haar_base_gt_one.le) (fun x => f x i))

end ASDExplicitGamma.Scalar
