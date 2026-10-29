module

public import ASDExplicitGamma.Gaussian.SupMeanDyadicConvergence
public import Mathlib.Topology.ContinuousMap.Compact

/-! Deterministic center chaining and dense-grid convergence for actual continuous tensor norms. -/
@[expose] public section
namespace ASDExplicitGamma.Gaussian
open Filter
open scoped Topology
noncomputable section

instance supMeanDyadicIndexNonempty (n : ℕ) : Nonempty (SupMeanDyadicIndex n) :=
  ⟨fun _ => ⟨0,by positivity⟩⟩

/-- Actual maximum of the tensor norm at all level-n centers. -/
def supMeanDyadicMaximum {E : Type*} [NormedAddCommGroup E]
    (c : Fin 2 → ℝ) (s : ℝ) (f : (Fin 2 → ℝ) → E) (n : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i : SupMeanDyadicIndex n => ‖f (supMeanDyadicCenter c s n i)‖)

/-- Actual maximum of all level-(n+1) center-to-parent tensor increments. -/
def supMeanDyadicIncrementMaximum {E : Type*} [NormedAddCommGroup E]
    (c : Fin 2 → ℝ) (s : ℝ) (f : (Fin 2 → ℝ) → E) (n : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i : SupMeanDyadicIndex (n+1) =>
    ‖f (supMeanDyadicCenter c s (n+1) i)-f (supMeanDyadicCenter c s n (supMeanDyadicParent i))‖)

/-- Every mesh norm is bounded by its actual finite maximum. -/
theorem supMean_dyadic_norm_le_max {E : Type*} [NormedAddCommGroup E]
    (c : Fin 2 → ℝ) (s : ℝ) (f : (Fin 2 → ℝ) → E) (n : ℕ) (i : SupMeanDyadicIndex n) :
    ‖f (supMeanDyadicCenter c s n i)‖ ≤ supMeanDyadicMaximum c s f n :=
  Finset.le_sup' (f := fun i : SupMeanDyadicIndex n => ‖f (supMeanDyadicCenter c s n i)‖) (Finset.mem_univ i)

/-- Finite mesh maxima are nonnegative. -/
theorem supMean_dyadic_max_nonneg {E : Type*} [NormedAddCommGroup E]
    (c : Fin 2 → ℝ) (s : ℝ) (f : (Fin 2 → ℝ) → E) (n : ℕ) :
    0 ≤ supMeanDyadicMaximum c s f n :=
  (norm_nonneg _).trans (supMean_dyadic_norm_le_max c s f n (Classical.choice inferInstance))

/-- The root mesh is precisely the original square center. -/
theorem supMean_dyadic_max_zero {E : Type*} [NormedAddCommGroup E]
    (c : Fin 2 → ℝ) (s : ℝ) (f : (Fin 2 → ℝ) → E) :
    supMeanDyadicMaximum c s f 0 = ‖f c‖ := by
  simp only [supMeanDyadicMaximum, supMean_dyadic_zero_center, Finset.sup'_const]

/-- One center refinement costs only the maximum of its actual parent increments. -/
theorem supMean_dyadic_max_parent_le {E : Type*} [NormedAddCommGroup E]
    (c : Fin 2 → ℝ) (s : ℝ) (f : (Fin 2 → ℝ) → E) (n : ℕ) :
    supMeanDyadicMaximum c s f (n+1) ≤
      supMeanDyadicMaximum c s f n+supMeanDyadicIncrementMaximum c s f n := by
  unfold supMeanDyadicMaximum
  apply Finset.sup'_le
  intro i _
  have hp := supMean_dyadic_norm_le_max c s f n (supMeanDyadicParent i)
  have hd : ‖f (supMeanDyadicCenter c s (n+1) i)-
      f (supMeanDyadicCenter c s n (supMeanDyadicParent i))‖ ≤ supMeanDyadicIncrementMaximum c s f n :=
    Finset.le_sup' (f := fun i : SupMeanDyadicIndex (n+1) =>
      ‖f (supMeanDyadicCenter c s (n+1) i)-f (supMeanDyadicCenter c s n (supMeanDyadicParent i))‖)
      (Finset.mem_univ i)
  have ht : ‖f (supMeanDyadicCenter c s (n+1) i)‖ ≤
      ‖f (supMeanDyadicCenter c s n (supMeanDyadicParent i))‖+
        ‖f (supMeanDyadicCenter c s (n+1) i)-f (supMeanDyadicCenter c s n (supMeanDyadicParent i))‖ := by
    calc
      _ = ‖f (supMeanDyadicCenter c s n (supMeanDyadicParent i))+
        (f (supMeanDyadicCenter c s (n+1) i)-f (supMeanDyadicCenter c s n (supMeanDyadicParent i)))‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  exact ht.trans (add_le_add hp hd)

/-- The finite center chain retains its literal root plus every refinement increment. -/
theorem supMean_dyadic_max_chain {E : Type*} [NormedAddCommGroup E]
    (c : Fin 2 → ℝ) (s : ℝ) (f : (Fin 2 → ℝ) → E) (N : ℕ) :
    supMeanDyadicMaximum c s f N ≤ ‖f c‖+
      ∑ n ∈ Finset.range N, supMeanDyadicIncrementMaximum c s f n := by
  induction N with
  | zero => simp only [supMean_dyadic_max_zero, Finset.sum_range_zero, add_zero, le_refl]
  | succ N ih =>
    calc
      _ ≤ supMeanDyadicMaximum c s f N+supMeanDyadicIncrementMaximum c s f N :=
        supMean_dyadic_max_parent_le c s f N
      _ ≤ (‖f c‖+∑ n ∈ Finset.range N, supMeanDyadicIncrementMaximum c s f n)+
          supMeanDyadicIncrementMaximum c s f N := by linarith only [ih]
      _ = _ := by rw [Finset.sum_range_succ]; ring

/-- The actual dense-center maximum converges to the genuine compact square
tensor supremum, so no supremum-integrability hypothesis is needed in its later passage. -/
theorem supMean_dyadic_maximum_tendsto {E : Type*} [NormedAddCommGroup E]
    (c : Fin 2 → ℝ) (s : ℝ) (hs : 0 < s) (f : (Fin 2 → ℝ) → E) (hf : Continuous f) :
    Tendsto (fun n => supMeanDyadicMaximum c s f n) atTop
      (𝓝 ‖(⟨fun x : supMeanClosedSquare c s => f x.val,
        hf.comp continuous_subtype_val⟩ : C(supMeanClosedSquare c s,E))‖) := by
  let hSquareNonempty : Nonempty (supMeanClosedSquare c s) :=
    ⟨⟨c,supMean_center_mem_closed_square c s hs.le⟩⟩
  let Z : C(supMeanClosedSquare c s,E) := ⟨fun x => f x.val,hf.comp continuous_subtype_val⟩
  obtain ⟨x,_,hx⟩ := isCompact_univ.exists_isMaxOn (Set.univ_nonempty : (Set.univ : Set (supMeanClosedSquare c s)).Nonempty)
    Z.continuous.norm.continuousOn
  have hnorm : ‖f x.val‖ = ‖Z‖ := by
    apply le_antisymm (Z.norm_coe_le_norm x)
    exact (ContinuousMap.norm_le Z (norm_nonneg _)).mpr (fun y => hx (Set.mem_univ y))
  have hlo : Tendsto (fun n => ‖f (supMeanDyadicCenter c s n (supMeanDyadicApproxIndex c s n x.val))‖)
      atTop (𝓝 ‖Z‖) := by
    have hh := ((hf.tendsto x.val).comp (supMean_dyadic_approx_tendsto c s hs x.val x.property)).norm
    simpa only [hnorm, Function.comp_def] using! hh
  have hhi (n : ℕ) : supMeanDyadicMaximum c s f n ≤ ‖Z‖ := by
    unfold supMeanDyadicMaximum
    apply Finset.sup'_le
    intro i _
    exact Z.norm_coe_le_norm ⟨supMeanDyadicCenter c s n i,supMean_dyadic_center_mem c s hs.le n i⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlo tendsto_const_nhds
    (fun n => supMean_dyadic_norm_le_max c s f n (supMeanDyadicApproxIndex c s n x.val)) hhi

end
end ASDExplicitGamma.Gaussian
