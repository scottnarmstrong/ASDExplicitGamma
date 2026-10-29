module

public import ASDExplicitGamma.Triadic.ScalarPositiveMultiplier
public import ASDExplicitGamma.Triadic.HaarNormTriangle

/-! Finite coordinate aggregation of sharp positive Haar multiplier bounds. -/

@[expose] public section
namespace ASDExplicitGamma.Triadic
open Homogenization MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

/-- Finite Minkowski aggregation with exact multiplicative constants. -/
theorem sqrt_finset_energy_bound {I : Type*} (s : Finset I) (E F G : I → ℝ) {M N : ℝ}
    (hM : 0 ≤ M) (hN : 0 ≤ N) (hE : ∀ i ∈ s, 0 ≤ E i)
    (hF : ∀ i ∈ s, 0 ≤ F i) (hG : ∀ i ∈ s, 0 ≤ G i)
    (hb : ∀ i ∈ s, Real.sqrt (E i) ≤ M*Real.sqrt (F i)+N*Real.sqrt (G i)) :
    Real.sqrt (∑ i ∈ s, E i) ≤ M*Real.sqrt (∑ i ∈ s, F i)+N*Real.sqrt (∑ i ∈ s, G i) := by
  have hsum : (∑ i ∈ s, E i) ≤ ∑ i ∈ s, (M*Real.sqrt (F i)+N*Real.sqrt (G i))^2 := by
    apply Finset.sum_le_sum
    intro i hi
    have h := pow_le_pow_left₀ (Real.sqrt_nonneg (E i)) (hb i hi) 2
    rwa [Real.sq_sqrt (hE i hi)] at h
  have h := (Real.sqrt_le_sqrt hsum).trans (sqrt_finset_sq_add_le s (fun i => M*Real.sqrt (F i)) (fun i => N*Real.sqrt (G i)))
  have hf : (∑ i ∈ s, (M*Real.sqrt (F i))^2) = M^2*∑ i ∈ s, F i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_pow, Real.sq_sqrt (hF i hi)]
  have hg : (∑ i ∈ s, (N*Real.sqrt (G i))^2) = N^2*∑ i ∈ s, G i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_pow, Real.sq_sqrt (hG i hi)]
  rwa [hf, hg, Real.sqrt_mul (sq_nonneg M), Real.sqrt_mul (sq_nonneg N), Real.sqrt_sq hM, Real.sqrt_sq hN] at h

/-- Scalar multiplication of an arbitrary finite-coordinate positive field, without H1 on that field. -/
theorem vectorPositiveHaar_mul_of_bounds {d m : ℕ} (Q : TriadicCube d) (η : H1Function (openCubeSet Q))
    (hη : MemLp η.toFun ⊤ (normalizedCubeMeasure Q))
    (hDη : ∀ i, MemLp (fun x => η.grad x i) ⊤ (normalizedCubeMeasure Q))
    (F : Vec d → Fin m → ℝ) (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (hP : ∀ i, Summable (fun k => (Real.sqrt 3)^(k+1)*energy Q (cubeIncrement Q (k+1) (fun x => F x i))))
    {A G : ℝ} (hA : 0 ≤ A) (hG : 0 ≤ G)
    (hb : ∀ᵐ x ∂normalizedCubeMeasure Q, |η.toFun x| ≤ A)
    (hg : ∀ᵐ x ∂normalizedCubeMeasure Q, (∑ i, (η.grad x i)^2) ≤ G^2) :
    (∀ i, Summable (fun k => (Real.sqrt 3)^(k+1)*energy Q (cubeIncrement Q (k+1) (fun x => η.toFun x*F x i)))) ∧
    vectorPositiveHaarNorm Q (fun x i => η.toFun x*F x i) ≤ A*vectorPositiveHaarNorm Q F+
      cubeScaleFactor Q*planarC1*G*Real.sqrt (∑ i, energy Q (fun x => F x i)) := by
  have hi (i : Fin m) := positiveHaar_mul_of_bounds Q η hη hDη (hF i) (hP i) hA hG hb hg
  refine ⟨fun i => (hi i).1, ?_⟩
  exact sqrt_finset_energy_bound Finset.univ
    (fun i => primalEnergy Q (Real.sqrt 3) (fun x => η.toFun x*F x i))
    (fun i => primalEnergy Q (Real.sqrt 3) (fun x => F x i))
    (fun i => energy Q (fun x => F x i)) hA (mul_nonneg (mul_nonneg (cubeScaleFactor_pos' Q).le (Real.sqrt_nonneg _)) hG)
    (fun i _ => primalEnergy_nonneg Q _ (Real.sqrt_nonneg _) _)
    (fun i _ => primalEnergy_nonneg Q _ (Real.sqrt_nonneg _) _) (fun i _ => energy_nonneg Q _)
    (fun i _ => (hi i).2)

/-- Positive Haar triangle inequality with actual convergence, coordinatewise. -/
theorem vectorPositiveHaar_add_le {d m : ℕ} (Q : TriadicCube d) (F G : Vec d → Fin m → ℝ)
    (hF : ∀ i, MemLp (fun x => F x i) 2 (normalizedCubeMeasure Q))
    (hG : ∀ i, MemLp (fun x => G x i) 2 (normalizedCubeMeasure Q))
    (hPF : ∀ i, Summable (fun k => (Real.sqrt 3)^(k+1)*energy Q (cubeIncrement Q (k+1) (fun x => F x i))))
    (hPG : ∀ i, Summable (fun k => (Real.sqrt 3)^(k+1)*energy Q (cubeIncrement Q (k+1) (fun x => G x i)))) :
    (∀ i, Summable (fun k => (Real.sqrt 3)^(k+1)*energy Q (cubeIncrement Q (k+1) (fun x => F x i+G x i)))) ∧
    vectorPositiveHaarNorm Q (fun x i => F x i+G x i) ≤ vectorPositiveHaarNorm Q F+vectorPositiveHaarNorm Q G := by
  have hi (i : Fin m) := positiveHaarNorm_add_le Q (hF i) (hG i) (hPF i) (hPG i)
  refine ⟨fun i => (hi i).1, ?_⟩
  have h := sqrt_finset_energy_bound Finset.univ
    (fun i => primalEnergy Q (Real.sqrt 3) (fun x => F x i+G x i))
    (fun i => primalEnergy Q (Real.sqrt 3) (fun x => F x i))
    (fun i => primalEnergy Q (Real.sqrt 3) (fun x => G x i)) (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (0:ℝ) ≤ 1)
    (fun i _ => primalEnergy_nonneg Q _ (Real.sqrt_nonneg _) _)
    (fun i _ => primalEnergy_nonneg Q _ (Real.sqrt_nonneg _) _)
    (fun i _ => primalEnergy_nonneg Q _ (Real.sqrt_nonneg _) _)
    (fun i _ => by simpa only [one_mul, positiveHaarNorm] using (hi i).2)
  simpa only [one_mul, vectorPositiveHaarNorm, vectorPositiveHaarEnergy] using h

end
end ASDExplicitGamma.Triadic
