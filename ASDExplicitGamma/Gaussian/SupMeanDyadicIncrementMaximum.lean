module

public import ASDExplicitGamma.Gaussian.SupMeanDyadicExpectation
public import ASDExplicitGamma.Gaussian.SupMeanDyadicLogCard
public import ASDExplicitGamma.Gaussian.SupMeanCenteredMGF

/-! Sharp finite mesh maxima for the actual dyadic center-to-parent tensor increments. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open MeasureTheory
noncomputable section

/-- The dyadic finite-maximum step uses the full 4^(n+1) population, the exact
increment mean cap, and the sharp centered Gaussian MGF; no independence is used. -/
theorem supMean_dyadic_increment_maximum_mean {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (c : Fin 2 → ℝ) (s : ℝ)
    (f : Ω → (Fin 2 → ℝ) → E) (hpoint : ∀ x, Integrable (fun ω => f ω x) μ)
    (hpointm : ∀ x, Measurable (fun ω => f ω x)) (n : ℕ) (m L : ℝ) (hL : 0 < L)
    (hmean : ∀ i : SupMeanDyadicIndex (n+1), (∫ ω, ‖f ω (supMeanDyadicCenter c s (n+1) i)-
      f ω (supMeanDyadicCenter c s n (supMeanDyadicParent i))‖ ∂μ) ≤ m)
    (hexp : ∀ lam > 0, ∀ i : SupMeanDyadicIndex (n+1),
      let X := fun ω => ‖f ω (supMeanDyadicCenter c s (n+1) i)-
        f ω (supMeanDyadicCenter c s n (supMeanDyadicParent i))‖
      Integrable (fun ω => Real.exp (lam*(X ω-∫ y, X y ∂μ))) μ ∧
      (∫ ω, Real.exp (lam*(X ω-∫ y, X y ∂μ)) ∂μ) ≤ Real.exp (lam^2*L^2/2)) :
    (∫ ω, supMeanDyadicIncrementMaximum c s (f ω) n ∂μ) ≤
      m+2*L*Real.sqrt (Real.log 2)*Real.sqrt (n+1:ℝ) := by
  let X := fun (i : SupMeanDyadicIndex (n+1)) ω => ‖f ω (supMeanDyadicCenter c s (n+1) i)-
    f ω (supMeanDyadicCenter c s n (supMeanDyadicParent i))‖
  have hXm (i : SupMeanDyadicIndex (n+1)) : Measurable (X i) :=
    ((hpointm _).sub (hpointm _)).norm
  have hXi (i : SupMeanDyadicIndex (n+1)) : Integrable (X i) μ := ((hpoint _).sub (hpoint _)).norm
  have hraw (lam : ℝ) (hlam : 0 < lam) (i : SupMeanDyadicIndex (n+1)) :
      Integrable (fun ω => Real.exp (lam*X i ω)) μ ∧
      (∫ ω, Real.exp (lam*X i ω) ∂μ) ≤ Real.exp (lam*m+lam^2*L^2/2) :=
    supMean_raw_mgf_of_centered μ (X i) lam m (L^2) hlam.le (hmean i) (hexp lam hlam i).1 (hexp lam hlam i).2
  have hb := supMean_finite_max_subgaussian μ Finset.univ Finset.univ_nonempty
    (by simpa only [Finset.card_univ] using supMean_dyadic_child_card_ge_two n)
    X hXm (fun i _ => hXi i) m L hL (fun lam hlam i _ => (hraw lam hlam i).1)
    (fun lam hlam i _ => (hraw lam hlam i).2)
  have he : supMeanFiniteMaximum Finset.univ Finset.univ_nonempty X =
      (fun ω => supMeanDyadicIncrementMaximum c s (f ω) n) := by
    funext ω
    unfold supMeanFiniteMaximum supMeanDyadicIncrementMaximum
    exact Finset.sup'_apply Finset.univ_nonempty X ω
  rw [he, Finset.card_univ, supMean_dyadic_log_card_sqrt] at hb
  exact hb.trans_eq (by ring)

end
end ASDExplicitGamma.Gaussian
