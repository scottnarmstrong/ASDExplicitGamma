module

public import ASDExplicitGamma.Native.HeatInitialMoments
public import ASDExplicitGamma.Native.HeatFiniteBandCenters
public import ASDExplicitGamma.Numerics.Native.HeatParametersData

/-! Generated Gaussian moment table dominates the product of its factors. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open ASDExplicitGamma.Numerics.Native

private def nativeHeatGaussianPrefixMoments (variance spectral : ℚ) (n : ℕ) :
    List ℚ :=
  (List.range n).foldl
    (fun qm j => nativeGaussianMomentStep variance spectral qm (j + 1)) [1]

private theorem nativeHeatGaussianPrefixMoments_succ (variance spectral : ℚ) (n : ℕ) :
    nativeHeatGaussianPrefixMoments variance spectral (n + 1) =
      nativeGaussianMomentStep variance spectral
        (nativeHeatGaussianPrefixMoments variance spectral n) (n + 1) := by
  simp [nativeHeatGaussianPrefixMoments, List.range_succ, List.foldl_append]

private theorem nativeHeatGaussianPrefixMoments_length
    (variance spectral : ℚ) (n : ℕ) :
    (nativeHeatGaussianPrefixMoments variance spectral n).length = n + 1 := by
  induction n with
  | zero => simp [nativeHeatGaussianPrefixMoments]
  | succ n ih =>
      rw [nativeHeatGaussianPrefixMoments_succ]
      simp [nativeGaussianMomentStep, ih]

private theorem nativeHeat_list_getLast_eq_getD
    (l : List ℚ) (n : ℕ) (hlen : l.length = n + 1) :
    l.getLast! = l.getD n 0 := by
  induction l generalizing n with
  | nil => simp at hlen
  | cons a t ih =>
      cases t with
      | nil =>
          have h : 1 = n + 1 := by simpa using hlen
          have hn : n = 0 := by omega
          subst n
          simp
      | cons b t =>
          have hlen' : t.length + 2 = n + 1 := by simpa using hlen
          have hn : 0 < n := by omega
          obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
          have htail : (b :: t).length = j + 1 := by
            simp only [List.length_cons]
            omega
          calc
            (a :: b :: t).getLast! = (b :: t).getLast! := by simp
            _ = (b :: t).getD j 0 := ih j htail
            _ = (a :: b :: t).getD (j + 1) 0 := by simp

private theorem nativeHeatGaussianPrefixMoments_last
    (variance spectral : ℚ) (n : ℕ) :
    (nativeHeatGaussianPrefixMoments variance spectral n).getLast! =
      (nativeHeatGaussianPrefixMoments variance spectral n).getD n 0 := by
  exact nativeHeat_list_getLast_eq_getD _ n
    (nativeHeatGaussianPrefixMoments_length variance spectral n)

private theorem nativeHeatGaussianPrefixMoments_getD_succ
    (variance spectral : ℚ) (n : ℕ) :
    (nativeHeatGaussianPrefixMoments variance spectral (n + 1)).getD (n + 1) 0 =
      nativeUp ((nativeHeatGaussianPrefixMoments variance spectral n).getD n 0 *
        (variance + 2 * (n : ℚ) * spectral)) := by
  rw [nativeHeatGaussianPrefixMoments_succ]
  have hlen := nativeHeatGaussianPrefixMoments_length variance spectral n
  have hlast := nativeHeatGaussianPrefixMoments_last variance spectral n
  calc
    _ = nativeUp ((nativeHeatGaussianPrefixMoments variance spectral n).getLast! *
          (variance + 2 * ((n + 1) - 1 : ℕ) * spectral)) := by
            simp [nativeGaussianMomentStep, hlen]
    _ = nativeUp ((nativeHeatGaussianPrefixMoments variance spectral n).getD n 0 *
          (variance + 2 * (n : ℚ) * spectral)) := by
            rw [hlast]
            congr 1

private theorem nativeGaussianMomentStep_fold_getD
    (variance spectral : ℚ) (qm : List ℚ) (r : ℕ) (hr : r < qm.length)
    (js : List ℕ) :
    (js.foldl (fun qm j => nativeGaussianMomentStep variance spectral qm (j + 1)) qm).getD r 0 =
      qm.getD r 0 := by
  induction js generalizing qm with
  | nil => rfl
  | cons j js ih =>
      rw [List.foldl_cons]
      have hlen : r <
          (nativeGaussianMomentStep variance spectral qm (j + 1)).length := by
        simp [nativeGaussianMomentStep]
        omega
      calc
        _ = (nativeGaussianMomentStep variance spectral qm (j + 1)).getD r 0 :=
          ih (nativeGaussianMomentStep variance spectral qm (j + 1)) hlen
        _ = qm.getD r 0 := by
          unfold nativeGaussianMomentStep
          exact List.getD_append _ _ _ _ hr

private theorem nativeGaussianMoments_getD_eq_prefix
    (variance spectral : ℚ) (r : ℕ) (hr : r ≤ 20) :
    (nativeGaussianMoments variance spectral).getD r 0 =
      (nativeHeatGaussianPrefixMoments variance spectral r).getD r 0 := by
  change ((List.range 20).foldl
      (fun qm j => nativeGaussianMomentStep variance spectral qm (j + 1)) [1]).getD r 0 =
    ((List.range r).foldl
      (fun qm j => nativeGaussianMomentStep variance spectral qm (j + 1)) [1]).getD r 0
  have hrange : List.range 20 = List.range r ++ List.range' r (20 - r) := by
    calc
      List.range 20 = List.range' 0 20 := List.range_eq_range'
      _ = List.range' 0 r ++ List.range' (0 + r) (20 - r) := by
        conv_lhs => rw [← Nat.add_sub_of_le hr]
        exact (List.range'_append_1 (s := 0) (m := r) (n := 20 - r)).symm
      _ = List.range r ++ List.range' r (20 - r) := by
        rw [← List.range_eq_range']
        simp only [Nat.zero_add]
  change ((List.range 20).foldl
      (fun qm j => nativeGaussianMomentStep variance spectral qm (j + 1)) [1]).getD r 0 =
    ((List.range r).foldl
      (fun qm j => nativeGaussianMomentStep variance spectral qm (j + 1)) [1]).getD r 0
  rw [hrange, List.foldl_append]
  have hlenEq :
      ((List.range r).foldl
        (fun qm j => nativeGaussianMomentStep variance spectral qm (j + 1)) [1]).length =
        r + 1 := by
    simpa [nativeHeatGaussianPrefixMoments] using
      nativeHeatGaussianPrefixMoments_length variance spectral r
  have hlen : r < ((List.range r).foldl
      (fun qm j => nativeGaussianMomentStep variance spectral qm (j + 1)) [1]).length := by
    omega
  exact nativeGaussianMomentStep_fold_getD variance spectral _ r hlen _

private theorem nativeHeatGaussianPrefixMoments_product_le
    (variance spectral : ℚ) (hvariance : 0 ≤ variance)
    (hspectral : 0 ≤ spectral) (r : ℕ) :
    ∏ i ∈ Finset.range r, (variance + 2 * (i : ℚ) * spectral) ≤
      (nativeHeatGaussianPrefixMoments variance spectral r).getD r 0 := by
  induction r with
  | zero => simp [nativeHeatGaussianPrefixMoments]
  | succ r ih =>
      rw [Finset.prod_range_succ]
      have hfactor : 0 ≤ variance + 2 * (r : ℚ) * spectral := by positivity
      have hprod : 0 ≤ ∏ i ∈ Finset.range r,
          (variance + 2 * (i : ℚ) * spectral) :=
        Finset.prod_nonneg fun i hi => by positivity
      calc
        (∏ i ∈ Finset.range r, (variance + 2 * (i : ℚ) * spectral)) *
            (variance + 2 * (r : ℚ) * spectral) ≤
          (nativeHeatGaussianPrefixMoments variance spectral r).getD r 0 *
            (variance + 2 * (r : ℚ) * spectral) :=
          mul_le_mul_of_nonneg_right ih hfactor
        _ ≤ nativeUp ((nativeHeatGaussianPrefixMoments variance spectral r).getD r 0 *
            (variance + 2 * (r : ℚ) * spectral)) := nativeUp_ge _
        _ = (nativeHeatGaussianPrefixMoments variance spectral (r + 1)).getD (r + 1) 0 :=
          (nativeHeatGaussianPrefixMoments_getD_succ variance spectral r).symm

theorem nativeGaussianMoments_product_le
    (variance spectral : ℚ) (hvariance : 0 ≤ variance)
    (hspectral : 0 ≤ spectral) (r : ℕ) (hr : r ≤ 20) :
    ∏ i ∈ Finset.range r, (variance + 2 * (i : ℚ) * spectral) ≤
      (nativeGaussianMoments variance spectral).getD r 0 := by
  calc
    ∏ i ∈ Finset.range r, (variance + 2 * (i : ℚ) * spectral) ≤
        (nativeHeatGaussianPrefixMoments variance spectral r).getD r 0 :=
      nativeHeatGaussianPrefixMoments_product_le variance spectral hvariance hspectral r
    _ = (nativeGaussianMoments variance spectral).getD r 0 :=
      (nativeGaussianMoments_getD_eq_prefix variance spectral r hr).symm

end ASDExplicitGamma.Native
