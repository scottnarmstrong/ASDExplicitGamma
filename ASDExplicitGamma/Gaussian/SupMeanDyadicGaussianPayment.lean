module

public import ASDExplicitGamma.Gaussian.SupMeanDyadicIncrementMaximum
public import ASDExplicitGamma.Gaussian.SupMeanDyadicSquareRoots

/-! Exact source dyadic payments from genuine tensor increment means and sharp MGF bounds. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open MeasureTheory
noncomputable section

/-- The full refinement maximum retains the source mean/metric payment at every
depth; all observations are of the actual field on the actual square. -/
theorem supMean_dyadic_gaussian_increment_payment {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (c : Fin 2 → ℝ) (s : ℝ) (hs : 0 < s)
    (f : Ω → (Fin 2 → ℝ) → E) (hpoint : ∀ x, Integrable (fun ω => f ω x) μ)
    (hpointm : ∀ x, Measurable (fun ω => f ω x)) (T V A : ℝ) (hT : 0 ≤ T) (hV : 0 < V) (hA : 0 < A)
    (hmean : ∀ x y : Fin 2 → ℝ, (∫ ω, ‖f ω y-f ω x‖ ∂μ) ≤
      Real.sqrt ((T/2)*V*((y-x) 0^2+(y-x) 1^2)))
    (hmgf : ∀ x y : Fin 2 → ℝ, ∀ lam > 0,
      let X := fun ω => ‖f ω y-f ω x‖
      Integrable (fun ω => Real.exp (lam*(X ω-∫ z, X z ∂μ))) μ ∧
      (∫ ω, Real.exp (lam*(X ω-∫ z, X z ∂μ)) ∂μ) ≤
        Real.exp (lam^2*((A^2*V)*((y-x) 0^2+(y-x) 1^2))/2)) (n : ℕ) :
    (∫ ω, supMeanDyadicIncrementMaximum c s (f ω) n ∂μ) ≤
      (s*Real.sqrt V)*supMeanDyadicIncrementPayment (Real.sqrt T) A n := by
  let B := s*Real.sqrt V
  let m := B*Real.sqrt T*supMeanDyadicMeanScale n
  let L := B*A*supMeanDyadicMetricScale n
  have hB : 0 < B := mul_pos hs (Real.sqrt_pos.mpr hV)
  have hL : 0 < L := mul_pos (mul_pos hB hA) (supMean_dyadic_metric_scale_pos n)
  have hd (i : SupMeanDyadicIndex (n+1)) :
      (supMeanDyadicCenter c s (n+1) i-supMeanDyadicCenter c s n (supMeanDyadicParent i)) 0^2+
        (supMeanDyadicCenter c s (n+1) i-supMeanDyadicCenter c s n (supMeanDyadicParent i)) 1^2 =
          2*s^2/((2:ℝ)^(n+2))^2 := by
    simpa only [Fin.sum_univ_two, Pi.sub_apply] using! supMean_dyadic_parent_distance_sq c s n i
  have hm (i : SupMeanDyadicIndex (n+1)) :
      (∫ ω, ‖f ω (supMeanDyadicCenter c s (n+1) i)-
        f ω (supMeanDyadicCenter c s n (supMeanDyadicParent i))‖ ∂μ) ≤ m := by
    have hh := hmean (supMeanDyadicCenter c s n (supMeanDyadicParent i)) (supMeanDyadicCenter c s (n+1) i)
    rw [hd, supMean_dyadic_mean_root T V s hT hV.le hs.le n] at hh
    exact hh
  have hLs : L^2 = (A^2*V)*(2*s^2/((2:ℝ)^(n+2))^2) := by
    have he : L = Real.sqrt ((A^2*V)*(2*s^2/((2:ℝ)^(n+2))^2)) :=
      (supMean_dyadic_metric_root A V s hA.le hV.le hs.le n).symm
    rw [he, Real.sq_sqrt (by positivity)]
  have he (lam : ℝ) (hlam : 0 < lam) (i : SupMeanDyadicIndex (n+1)) :
      let X := fun ω => ‖f ω (supMeanDyadicCenter c s (n+1) i)-
        f ω (supMeanDyadicCenter c s n (supMeanDyadicParent i))‖
      Integrable (fun ω => Real.exp (lam*(X ω-∫ z, X z ∂μ))) μ ∧
      (∫ ω, Real.exp (lam*(X ω-∫ z, X z ∂μ)) ∂μ) ≤ Real.exp (lam^2*L^2/2) := by
    have hh := hmgf (supMeanDyadicCenter c s n (supMeanDyadicParent i))
      (supMeanDyadicCenter c s (n+1) i) lam hlam
    rw [hd, ← hLs] at hh
    exact hh
  calc
    _ ≤ m+2*L*Real.sqrt (Real.log 2)*Real.sqrt (n+1:ℝ) :=
      supMean_dyadic_increment_maximum_mean μ c s f hpoint hpointm n m L hL hm he
    _ = _ := by unfold m L B supMeanDyadicIncrementPayment; ring

end
end ASDExplicitGamma.Gaussian
