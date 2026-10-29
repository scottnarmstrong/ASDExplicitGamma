module

public import ASDExplicitGamma.Gaussian.HilbertBasisVariance

/-! Basis independence for complete physical projection traces. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open ASDExplicitGamma.Gaussian
noncomputable section

/-- Parseval makes each scalar observation independent of the input basis. -/
private theorem scalar_trace_basis {W E I J : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : W →L[ℝ] E) (e : HilbertBasis I ℝ W) (e' : HilbertBasis J ℝ W) (z : E) :
    (∑' i, (inner ℝ z (T (e i)))^2) = ∑' i, (inner ℝ z (T (e' i)))^2 := by
  let l : W →L[ℝ] ℝ := (innerSL ℝ z).comp T
  change (∑' i, (l (e i))^2) = ∑' i, (l (e' i))^2
  exact (hilbertBasis_variance e l).trans (hilbertBasis_variance e' l).symm

/-- Absolute square summability of the two-index Parseval expansion. -/
private theorem double_trace_summable {W E I K : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : W →L[ℝ] E) (e : HilbertBasis I ℝ W) (f : HilbertBasis K ℝ E)
    (he : Summable (fun i => ‖T (e i)‖^2)) :
    Summable (fun p : I × K => (inner ℝ (f p.2) (T (e p.1)))^2) := by
  rw [summable_prod_of_nonneg (fun _ => sq_nonneg _)]
  refine ⟨fun i => hilbertBasis_summable_sq f (T (e i)),?_⟩
  have hrow : (fun i => ∑' k, (inner ℝ (f k) (T (e i)))^2) =
      fun i => ‖T (e i)‖^2 := funext (fun i => hilbertBasis_norm_sq f (T (e i)))
  rw [hrow]
  exact he

/-- The square trace of a genuine operator is independent of the complete
input Hilbert basis. Both convergence statements concern that same operator. -/
theorem parent_boundary_operator_sq_trace_with_output_basis {W E I J K : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : W →L[ℝ] E) (e : HilbertBasis I ℝ W) (e' : HilbertBasis J ℝ W)
    (f : HilbertBasis K ℝ E)
    (he : Summable (fun i => ‖T (e i)‖^2))
    (he' : Summable (fun i => ‖T (e' i)‖^2)) :
    (∑' i, ‖T (e i)‖^2) = ∑' i, ‖T (e' i)‖^2 := by
  have hd := double_trace_summable T e f he
  have hd' := double_trace_summable T e' f he'
  calc
    _ = ∑' i, ∑' k, (inner ℝ (f k) (T (e i)))^2 :=
      tsum_congr (fun i => (hilbertBasis_norm_sq f (T (e i))).symm)
    _ = ∑' k, ∑' i, (inner ℝ (f k) (T (e i)))^2 := (Summable.tsum_comm (f := fun i k => (inner ℝ (f k) (T (e i)))^2) hd).symm
    _ = ∑' k, ∑' i, (inner ℝ (f k) (T (e' i)))^2 :=
      tsum_congr (fun k => scalar_trace_basis T e e' (f k))
    _ = ∑' i, ∑' k, (inner ℝ (f k) (T (e' i)))^2 := Summable.tsum_comm (f := fun i k => (inner ℝ (f k) (T (e' i)))^2) hd'
    _ = _ := tsum_congr (fun i => hilbertBasis_norm_sq f (T (e' i)))

/-- Complete square trace independence, with no selected output basis in
its interface. -/
theorem parent_boundary_operator_sq_trace_basis {W E I J : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : W →L[ℝ] E) (e : HilbertBasis I ℝ W) (e' : HilbertBasis J ℝ W)
    (he : Summable (fun i => ‖T (e i)‖^2))
    (he' : Summable (fun i => ‖T (e' i)‖^2)) :
    (∑' i, ‖T (e i)‖^2) = ∑' i, ‖T (e' i)‖^2 := by
  obtain ⟨K,f,_⟩ := exists_hilbertBasis ℝ E
  exact parent_boundary_operator_sq_trace_with_output_basis T e e' f he he'

end
end ASDExplicitGamma.Native
