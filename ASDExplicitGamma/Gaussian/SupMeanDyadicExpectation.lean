module

public import ASDExplicitGamma.Gaussian.SupMeanDyadicMaxima
public import ASDExplicitGamma.Gaussian.SupMeanFinite
public import ASDExplicitGamma.Gaussian.SupMeanNonnegativeLimit

/-! The exact dyadic expectation passage derives integrability of the compact tensor supremum. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open MeasureTheory Filter
open scoped Topology
noncomputable section

/-- Actual finite mesh maxima are integrable from the pointwise tensor integrability. -/
theorem supMean_dyadic_maximum_integrable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) (c : Fin 2 → ℝ) (s : ℝ) (f : Ω → (Fin 2 → ℝ) → E)
    (hpoint : ∀ x, Integrable (fun ω => f ω x) μ) (n : ℕ) :
    Integrable (fun ω => supMeanDyadicMaximum c s (f ω) n) μ := by
  have hh := supMean_finite_max_integrable μ Finset.univ Finset.univ_nonempty
    (fun (i : SupMeanDyadicIndex n) ω => ‖f ω (supMeanDyadicCenter c s n i)‖)
    (fun i _ => (hpoint _).norm)
  convert hh using 1
  funext ω
  unfold supMeanDyadicMaximum supMeanFiniteMaximum
  exact (Finset.sup'_apply Finset.univ_nonempty
    (fun (i : SupMeanDyadicIndex n) (ω : Ω) => ‖f ω (supMeanDyadicCenter c s n i)‖) ω).symm

/-- The full actual center-to-parent increment maximum is integrable as well. -/
theorem supMean_dyadic_increment_maximum_integrable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) (c : Fin 2 → ℝ) (s : ℝ) (f : Ω → (Fin 2 → ℝ) → E)
    (hpoint : ∀ x, Integrable (fun ω => f ω x) μ) (n : ℕ) :
    Integrable (fun ω => supMeanDyadicIncrementMaximum c s (f ω) n) μ := by
  have hh := supMean_finite_max_integrable μ Finset.univ Finset.univ_nonempty
    (fun (i : SupMeanDyadicIndex (n+1)) ω => ‖f ω (supMeanDyadicCenter c s (n+1) i)-
      f ω (supMeanDyadicCenter c s n (supMeanDyadicParent i))‖)
    (fun i _ => ((hpoint _).sub (hpoint _)).norm)
  convert hh using 1
  funext ω
  unfold supMeanDyadicIncrementMaximum supMeanFiniteMaximum
  exact (Finset.sup'_apply Finset.univ_nonempty
    (fun (i : SupMeanDyadicIndex (n+1)) (ω : Ω) => ‖f ω (supMeanDyadicCenter c s (n+1) i)-
      f ω (supMeanDyadicCenter c s n (supMeanDyadicParent i))‖) ω).symm

/-- Finite mesh increment estimates and dense-center convergence prove the full
compact supremum estimate and its integrability, rather than assuming the latter. -/
theorem supMean_dyadic_expectation_limit {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    (μ : Measure Ω) (c : Fin 2 → ℝ) (s : ℝ) (hs : 0 < s) (f : Ω → (Fin 2 → ℝ) → E)
    (hf : ∀ ω, Continuous (f ω)) (hpoint : ∀ x, Integrable (fun ω => f ω x) μ)
    (a C : ℝ) (p : ℕ → ℝ) (hC : 0 ≤ C)
    (hbase : (∫ ω, ‖f ω c‖ ∂μ) ≤ a)
    (hinc : ∀ n, (∫ ω, supMeanDyadicIncrementMaximum c s (f ω) n ∂μ) ≤ p n)
    (hpay : ∀ n, a+(∑ k ∈ Finset.range n, p k) ≤ C) :
    Integrable (fun ω => ‖(⟨fun x : supMeanClosedSquare c s => f ω x.val,
      (hf ω).comp continuous_subtype_val⟩ : C(supMeanClosedSquare c s,E))‖) μ ∧
    (∫ ω, ‖(⟨fun x : supMeanClosedSquare c s => f ω x.val,
      (hf ω).comp continuous_subtype_val⟩ : C(supMeanClosedSquare c s,E))‖ ∂μ) ≤ C := by
  have hmesh (n : ℕ) := supMean_dyadic_maximum_integrable μ c s f hpoint n
  have hincs (n : ℕ) := supMean_dyadic_increment_maximum_integrable μ c s f hpoint n
  apply supMean_nonnegative_integral_limit μ
    (fun n ω => supMeanDyadicMaximum c s (f ω) n) _ C hC hmesh
    (fun n => Eventually.of_forall fun ω => supMean_dyadic_max_nonneg c s (f ω) n)
    (Eventually.of_forall fun ω => norm_nonneg _) _
    (Eventually.of_forall fun ω => supMean_dyadic_maximum_tendsto c s hs (f ω) (hf ω))
  intro n
  have hsum : Integrable (fun ω => ∑ k ∈ Finset.range n, supMeanDyadicIncrementMaximum c s (f ω) k) μ :=
    integrable_finsetSum (Finset.range n) (fun k _ => hincs k)
  have hdom : Integrable (fun ω => ‖f ω c‖+
      ∑ k ∈ Finset.range n, supMeanDyadicIncrementMaximum c s (f ω) k) μ := by
    simpa only [Pi.add_apply] using! (hpoint c).norm.add hsum
  calc
    _ ≤ ∫ ω, ‖f ω c‖+∑ k ∈ Finset.range n, supMeanDyadicIncrementMaximum c s (f ω) k ∂μ :=
      integral_mono (hmesh n) hdom (fun ω => supMean_dyadic_max_chain c s (f ω) n)
    _ = (∫ ω, ‖f ω c‖ ∂μ)+∑ k ∈ Finset.range n, ∫ ω, supMeanDyadicIncrementMaximum c s (f ω) k ∂μ := by
      rw [integral_add (f := fun ω => ‖f ω c‖)
        (g := fun ω => ∑ k ∈ Finset.range n, supMeanDyadicIncrementMaximum c s (f ω) k)
        (hpoint c).norm hsum, integral_finsetSum (Finset.range n) (fun k _ => hincs k)]
    _ ≤ a+∑ k ∈ Finset.range n, p k :=
      add_le_add hbase (Finset.sum_le_sum (fun k _ => hinc k))
    _ ≤ C := hpay n

end
end ASDExplicitGamma.Gaussian
