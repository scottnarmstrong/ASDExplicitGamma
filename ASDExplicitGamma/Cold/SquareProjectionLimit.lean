module

public import ASDExplicitGamma.Cold.RatioNineProjection
public import Homogenization.Besov.Duality.ProjectionLimit

/-! # Strong L² convergence of the actual cell projections -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Filter Topology
open ASDExplicitGamma.Triadic
open scoped BigOperators ENNReal
namespace ASDExplicitGamma.Cold

/-- Squared norm of an actual real L² element in spatial representatives. -/
theorem norm_sq_toLp_real {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : MemLp f 2 μ) : ‖hf.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

/-- Strong convergence follows from the actual squared L² differences. -/
theorem tendsto_toLp_of_integral_sq_sub_tendsto_zero {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} {l : Filter ι} {f : ι → α → ℝ} {g : α → ℝ}
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ)
    (h : Tendsto (fun n => ∫ x, (f n x - g x) ^ 2 ∂μ) l (𝓝 0)) :
    Tendsto (fun n => (hf n).toLp (f n)) l (𝓝 (hg.toLp g)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hn (n : ι) : ‖(hf n).toLp (f n) - hg.toLp g‖ =
      Real.sqrt (∫ x, (f n x - g x) ^ 2 ∂μ) := by
    rw [← MemLp.toLp_sub (hf n) hg]
    change ‖((hf n).sub hg).toLp (f n - g)‖ = Real.sqrt (∫ x, (f n - g) x ^ 2 ∂μ)
    rw [← norm_sq_toLp_real ((hf n).sub hg),
      Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
  simp_rw [hn]
  simpa using h.sqrt

/-- Projected energies converge to the full L² energy. -/
theorem tendsto_energy_squareProjection_scalar (Q : TriadicCube 2) {f : Vec 2 → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    Tendsto (fun n => energy Q (cubeProjection Q n f)) atTop (𝓝 (energy Q f)) := by
  have hc : cubeBesovConjExponent (2 : ℝ≥0∞) = 2 := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  have h := tendsto_cubeBesovPairing_projection_left_of_memLp Q (2 : ℝ≥0∞) f f hf
    (by simpa only [hc] using hf) (by norm_num) (by norm_num) (by rw [hc]; norm_num)
  have heq (n : ℕ) : cubeBesovPairing Q (cubeProjection Q (n+1) f) f =
      energy Q (cubeProjection Q (n+1) f) := by
    change pairing Q (cubeProjection Q (n+1) f) f = _
    rw [pairing_comm, pairing_projection_energy Q _ hf]
  simp_rw [heq] at h
  exact (Filter.tendsto_add_atTop_iff_nat 1).1 h

/-- The residual of the actual depth-n cell projection tends strongly to zero. -/
theorem tendsto_energy_projection_residual (Q : TriadicCube 2) {f : Vec 2 → ℝ}
    (hf : MemLp f 2 (normalizedCubeMeasure Q)) :
    Tendsto (fun n => energy Q (fun x => f x - cubeProjection Q n f x)) atTop (𝓝 0) := by
  simp_rw [energy_residual Q _ hf]
  simpa using (tendsto_const_nhds (x := energy Q f)).sub
    (tendsto_energy_squareProjection_scalar Q hf)

/-- The vector version is the finite sum of the actual coordinate residuals. -/
theorem tendsto_squareVectorEnergy_projection_residual (Q : TriadicCube 2)
    {G : Vec 2 → Vec 2} (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q)) :
    Tendsto (fun n => squareVectorEnergy Q (fun x => G x - squareProjection Q n G x))
      atTop (𝓝 0) := by
  have h := tendsto_finsetSum Finset.univ (fun i _ => tendsto_energy_projection_residual Q (hG i))
  simpa only [Finset.sum_const_zero, squareVectorEnergy, squareProjection, Pi.sub_apply] using h

end ASDExplicitGamma.Cold
