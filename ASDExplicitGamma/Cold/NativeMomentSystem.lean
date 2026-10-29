module

public import ASDExplicitGamma.Cold.NativeCellIndex
public import ASDExplicitGamma.Cold.ColdMomentTable

/-! # The actual fixed-native-model moment hierarchy -/

@[expose] public section
noncomputable section
open MeasureTheory Homogenization Algsuperdiff.Section3
open scoped ENNReal BigOperators
namespace ASDExplicitGamma.Cold

/-- Genuine child traces at every valid lag pair; unused reversed pairs use the root of that lag. -/
def coldNativeChildren (M : ABKModel 2) (m : ℤ) (k ell : ℕ) (i : Fin (9^(ell-k))) : Cutoff.CutoffSample 2 → ℝ :=
  if k ≤ ell then coldNativeCellTrace M m (coldNativeChildCell m k ell i) else coldNativeTrace M m k

/-- The literal four-colour partition of the valid native child array. -/
def coldNativeChildColor (m : ℤ) (k ell : ℕ) (i : Fin (9^(ell-k))) : Fin 4 :=
  if k ≤ ell then coldCubeColor (coldNativeChildCell m k ell i) else 0

/-- Every child trace has exactly its source lag law, including harmless unused reversed pairs. -/
theorem coldNativeChildren_sameLaw (M : ABKModel 2) (m : ℤ) (k ell : ℕ) (i : Fin (9^(ell-k))) :
    ProbabilityTheory.IdentDistrib (coldNativeChildren M m k ell i) (coldNativeTrace M m k)
      (Cutoff.cutoffSampleLaw M).toMeasure (Cutoff.cutoffSampleLaw M).toMeasure := by
  by_cases hk : k ≤ ell
  · have he := coldNativeChildCell_scale m hk i
    simpa only [coldNativeChildren,ite_eq_left hk,he,coldNativeTrace] using
      coldNativeCellTrace_identDistrib M m (coldNativeChildCell m k ell i)
  · rw [coldNativeChildren,ite_eq_right hk]
    exact ProbabilityTheory.IdentDistrib.refl (coldNativeTrace_measurable M m k).aemeasurable

/-- Native child arrays have the actual sharp four-colour independence. -/
theorem coldNativeChildren_independent (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (m : ℤ)
    {k ell : ℕ} (hk : k < ell) : ∀ c : Fin 4, ProbabilityTheory.iIndepFun
      (fun i : {i // coldNativeChildColor m k ell i = c} => coldNativeChildren M m k ell i.val)
      (Cutoff.cutoffSampleLaw M).toMeasure := by
  have hi := cold_native_trace_four_color M h hM m (m+(k:ℤ)) (by omega)
    (coldNativeChildCell m k ell) (coldNativeChildCell_injective m k ell)
    (coldNativeChildCell_scale m hk.le)
  have hcol : coldNativeChildColor m k ell = (fun i => coldCubeColor (coldNativeChildCell m k ell i)) := by
    funext i
    exact ite_eq_left hk.le
  have hchild : coldNativeChildren M m k ell = (fun i => coldNativeCellTrace M m (coldNativeChildCell m k ell i)) := by
    funext i
    exact ite_eq_left hk.le
  rw [hcol,hchild]
  exact hi

/-- Native subadditivity is the actual source finite-child average after exact reindexing. -/
theorem coldNativeChildren_subadditive (M : ABKModel 2) (m : ℤ) {k ell : ℕ} (hk : k < ell)
    (ω : Cutoff.CutoffSample 2) :
    coldNativeTrace M m ell ω ≤ (∑ i, coldNativeChildren M m k ell i ω)/((9:ℝ)^(ell-k)) := by
  let Q := originCube 2 (m+(ell:ℤ))
  have hsub := coldNativeCellTrace_subadditive M m Q (ell-k) ω
  have he : (∑ i : Fin (9^(ell-k)), coldNativeChildren M m k ell i ω) =
      ∑ C : SquareCells Q (ell-k), coldNativeCellTrace M m C.val ω := by
    simp only [coldNativeChildren,ite_eq_left hk.le,coldNativeChildCell]
    exact Equiv.sum_comp (coldCellEquiv Q (ell-k)) (fun C => coldNativeCellTrace M m C.val ω)
  rw [he]
  change coldNativeCellTrace M m Q ω ≤ _
  apply hsub.trans_eq
  unfold squareCellMean
  rw [descendantsAtDepth_card]
  norm_num only [Nat.reducePow,Nat.cast_pow,Nat.cast_ofNat]
  ring

/-- The source hierarchy at one actual fixed completed label. All locality, independence,
nonnegativity and subadditivity fields are proved from the q3 model and root input. -/
def coldNativeMomentSystem (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (m : ℤ)
    {R : ℝ} (hroot : root20 M m ≤ ENNReal.ofReal R) : ColdMomentSystem (Cutoff.CutoffSample 2) (Cutoff.cutoffSampleLaw M).toMeasure where
  trace := coldNativeTrace M m
  trace_memLp := coldNativeTrace_memLp hroot
  trace_nonneg := fun ell => Filter.Eventually.of_forall (coldNativeTrace_nonneg M m ell)
  children := coldNativeChildren M m
  sameLaw := coldNativeChildren_sameLaw M m
  color := coldNativeChildColor m
  independent := fun _ _ hk => coldNativeChildren_independent M h hM m hk
  subadditive := fun _ _ hk => Filter.Eventually.of_forall (coldNativeChildren_subadditive M m hk)

/-- Native checked moment caps through every lag <=128, using only genuinely earlier mean caps. -/
theorem cold_native_moment_table (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h) (m : ℤ)
    {θ : ℝ} (hθ : 0 ≤ θ)
    (hroot : root20 M m ≤ ENNReal.ofReal (θ*(Numerics.Cold.coldR20:ℝ))) {n : ℕ} (hn : n ≤ 128)
    (hmean : ∀ k < n, coldNativeMean M m k ≤ θ*(Numerics.Cold.coldMeanAt k:ℝ)) :
    lpNorm (coldNativeTrace M m n) 20 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      θ*(Numerics.Cold.coldMomentAt n:ℝ) := by
  exact cold_moment_table_caps (coldNativeMomentSystem M h hM m hroot) hθ
    (coldNativeTrace_zero_norm_le (mul_nonneg hθ (by norm_num [Numerics.Cold.coldR20])) hroot) hn hmean

end ASDExplicitGamma.Cold
