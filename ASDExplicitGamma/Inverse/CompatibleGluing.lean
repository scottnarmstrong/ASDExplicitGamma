module

public import ASDExplicitGamma.Inverse.CompatibleMidpoint
public import Homogenization.Sobolev.Truncation.H10Limit
public import Homogenization.Sobolev.Truncation.WeakGradientLimit
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! Countable H¹₀ gluing from a positive L² summability budget. -/

@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

local instance compatibleLpFactTwo : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

/-- The L² representative of one H¹ endpoint correction. -/
def compatibleFunctionLpTerm {U : Set (Vec 2)} (F : H1Function U) :
    Lp ℝ 2 (volumeMeasureOn U) := F.memL2.toLp F.toFun

/-- One L² gradient coordinate of an H¹ endpoint correction. -/
def compatibleGradientLpTerm {U : Set (Vec 2)} (F : H1Function U) (i : Fin 2) :
    Lp ℝ 2 (volumeMeasureOn U) := (F.gradMemL2 i).toLp (fun x => F.grad x i)

/-- Finite partial gluing of compatible corrections on the parent. -/
def compatiblePartialSum {U : Set (Vec 2)} (F : ℕ → H1Function U) (N : ℕ) :
    H1Function U := ∑ n ∈ Finset.range N, F n

theorem bank_h1_finset_sum_toFun {U : Set (Vec 2)} {ι : Type*}
    (F : ι → H1Function U) (s : Finset ι) :
    (∑ n ∈ s, F n).toFun = ∑ n ∈ s, (F n).toFun := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      funext x
      simp only [Finset.sum_insert ha, H1Function.add_toFun, Finset.sum_apply]
      have ihx : (∑ n ∈ s, F n).toFun x = ∑ n ∈ s, (F n).toFun x := by
        simpa only [Finset.sum_apply] using congrFun ih x
      exact congrArg (fun y => (F a).toFun x + y) ihx

theorem bank_h1_finset_sum_grad {U : Set (Vec 2)} {ι : Type*}
    (F : ι → H1Function U) (s : Finset ι) (i : Fin 2) :
    (fun x => (∑ n ∈ s, F n).grad x i) = fun x => ∑ n ∈ s, (F n).grad x i := by
  classical
  induction s using Finset.induction_on with
  | empty => funext x; simp
  | @insert a s ha ih =>
      funext x
      simp only [Finset.sum_insert ha, H1Function.add_grad, Pi.add_apply]
      have ihx : (∑ n ∈ s, F n).grad x i = ∑ n ∈ s, (F n).grad x i := by
        simpa only [Finset.sum_apply] using congrFun ih x
      exact congrArg (fun y => (F a).grad x i + y) ihx

theorem compatible_partial_sum_memH10 {U : Set (Vec 2)}
    (F : ℕ → H1Function U) (hF : ∀ n, MemH10 U (F n).toFun) (N : ℕ) :
    MemH10 U (compatiblePartialSum F N).toFun := by
  have hsum (s : Finset ℕ) : MemH10 U (∑ n ∈ s, (F n).toFun) := by
    classical
    induction s using Finset.induction_on with
    | empty => simpa using (memH10_zero : MemH10 U (0 : Vec 2 → ℝ))
    | @insert a s ha ih =>
        rw [Finset.sum_insert ha]
        exact memH10_add (hF a) ih
  rw [compatiblePartialSum, bank_h1_finset_sum_toFun]
  exact hsum (Finset.range N)

theorem compatible_partial_sum_function_toLp {U : Set (Vec 2)}
    (F : ℕ → H1Function U) (N : ℕ) :
    (compatiblePartialSum F N).memL2.toLp
        (compatiblePartialSum F N).toFun =
      ∑ n ∈ Finset.range N, compatibleFunctionLpTerm (F n) := by
  apply Lp.ext
  filter_upwards [
    (compatiblePartialSum F N).memL2.coeFn_toLp,
    ae_all_iff.mpr (fun n => (F n).memL2.coeFn_toLp),
    Lp.coeFn_finsetSum (Finset.range N)
      (fun n => compatibleFunctionLpTerm (F n))] with x hsum hterms hLpSum
  rw [hsum, compatiblePartialSum, bank_h1_finset_sum_toFun]
  rw [hLpSum]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro n hn
  exact (hterms n).symm

theorem lp_toLp_self {U : Set (Vec 2)}
    (f : Lp ℝ 2 (volumeMeasureOn U)) :
    (Lp.memLp f).toLp (fun x => f x) = f := by
  apply Lp.ext
  exact (Lp.memLp f).coeFn_toLp

theorem compatible_partial_sum_function_tendsto {U : Set (Vec 2)}
    (F : ℕ → H1Function U)
    (hfun : Summable (fun n => compatibleFunctionLpTerm (F n))) :
    Tendsto (fun N => (compatiblePartialSum F N).memL2.toLp
      (compatiblePartialSum F N).toFun) atTop
      (𝓝 (∑' n, compatibleFunctionLpTerm (F n))) := by
  have hs := hfun.hasSum.tendsto_sum_nat
  exact hs.congr' (Filter.Eventually.of_forall
    (fun N => (compatible_partial_sum_function_toLp F N).symm))

theorem compatible_partial_sum_gradient_toLp {U : Set (Vec 2)}
    (F : ℕ → H1Function U) (N : ℕ) (i : Fin 2) :
    ((compatiblePartialSum F N).gradMemL2 i).toLp
        (fun x => (compatiblePartialSum F N).grad x i) =
      ∑ n ∈ Finset.range N, compatibleGradientLpTerm (F n) i := by
  apply Lp.ext
  filter_upwards [
    (compatiblePartialSum F N).gradMemL2 i |>.coeFn_toLp,
    ae_all_iff.mpr (fun n => (F n).gradMemL2 i |>.coeFn_toLp),
    Lp.coeFn_finsetSum (Finset.range N)
      (fun n => compatibleGradientLpTerm (F n) i)] with x hsum hterms hLpSum
  rw [hsum, compatiblePartialSum]
  rw [congrFun (bank_h1_finset_sum_grad F (Finset.range N) i) x]
  rw [hLpSum]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro n hn
  exact (hterms n).symm

theorem compatible_partial_sum_gradient_tendsto {U : Set (Vec 2)}
    (F : ℕ → H1Function U) (hgrad : ∀ i, Summable
      (fun n => compatibleGradientLpTerm (F n) i)) (i : Fin 2) :
    Tendsto (fun N => ((compatiblePartialSum F N).gradMemL2 i).toLp
      (fun x => (compatiblePartialSum F N).grad x i)) atTop
      (𝓝 (∑' n, compatibleGradientLpTerm (F n) i)) := by
  have hs := (hgrad i).hasSum.tendsto_sum_nat
  exact hs.congr' (Filter.Eventually.of_forall
    (fun N => (compatible_partial_sum_gradient_toLp F N i).symm))

/-- The parent H¹ field obtained by summing all endpoint corrections in L²,
including every weak-gradient coordinate. -/
noncomputable def compatibleSeriesLimit {U : Set (Vec 2)}
    (F : ℕ → H1Function U)
    (hfun : Summable (fun n => compatibleFunctionLpTerm (F n)))
    (hgrad : ∀ i, Summable (fun n => compatibleGradientLpTerm (F n) i)) :
    H1Function U := by
  let f : Lp ℝ 2 (volumeMeasureOn U) := ∑' n, compatibleFunctionLpTerm (F n)
  let g : Fin 2 → Lp ℝ 2 (volumeMeasureOn U) := fun i =>
    ∑' n, compatibleGradientLpTerm (F n) i
  have hfpartial : Tendsto
      (fun N => (compatiblePartialSum F N).memL2.toLp
        (compatiblePartialSum F N).toFun) atTop (𝓝 f) := by
    simpa only [f] using compatible_partial_sum_function_tendsto F hfun
  have hgpartial (i : Fin 2) : Tendsto
      (fun N => ((compatiblePartialSum F N).gradMemL2 i).toLp
        (fun x => (compatiblePartialSum F N).grad x i)) atTop (𝓝 (g i)) := by
    simpa only [g] using compatible_partial_sum_gradient_tendsto F hgrad i
  have hfunConv : Tendsto
      (fun N => eLpNorm (fun x => (compatiblePartialSum F N).toFun x - f x)
        2 (volumeMeasureOn U)) atTop (𝓝 0) := by
    have hlim : (Lp.memLp f).toLp (fun x => f x) = f := lp_toLp_self f
    have hpartial : Tendsto
        (fun N => (compatiblePartialSum F N).memL2.toLp
          (compatiblePartialSum F N).toFun) atTop
        (𝓝 ((Lp.memLp f).toLp (fun x => f x))) := by
      simpa only [hlim] using hfpartial
    exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun N x => (compatiblePartialSum F N).toFun x)
      (fun N => (compatiblePartialSum F N).memL2)
      (fun x => f x) (Lp.memLp f)).mp hpartial
  have hgradConv (i : Fin 2) : Tendsto
      (fun N => eLpNorm
        (fun x => (compatiblePartialSum F N).grad x i - (g i) x)
        2 (volumeMeasureOn U)) atTop (𝓝 0) := by
    have hlim : (Lp.memLp (g i)).toLp (fun x => (g i) x) = g i :=
      lp_toLp_self (g i)
    have hpartial : Tendsto
        (fun N => ((compatiblePartialSum F N).gradMemL2 i).toLp
          (fun x => (compatiblePartialSum F N).grad x i)) atTop
        (𝓝 ((Lp.memLp (g i)).toLp (fun x => (g i) x))) := by
      simpa only [hlim] using hgpartial i
    exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun N x => (compatiblePartialSum F N).grad x i)
      (fun N => (compatiblePartialSum F N).gradMemL2 i)
      (fun x => (g i) x) (Lp.memLp (g i))).mp hpartial
  have hweak := HasWeakGradientOn.of_tendsto_eLpNorm_two
    (Lp.memLp f) (fun i => Lp.memLp (g i))
    (fun N => (compatiblePartialSum F N).memL2)
    (fun N i => (compatiblePartialSum F N).gradMemL2 i)
    (fun N => (compatiblePartialSum F N).hasWeakGradient)
    hfunConv hgradConv
  exact
    { toFun := f
      grad := fun x i => (g i) x
      memL2 := Lp.memLp f
      gradMemL2 := fun i => Lp.memLp (g i)
      hasWeakGradient := hweak }

theorem compatible_countable_h10_gluing {U : Set (Vec 2)}
    (hU : IsOpenBoundedConvexDomain U) (F : ℕ → H1Function U)
    (hF : ∀ n, MemH10 U (F n).toFun)
    (hfun : Summable (fun n => compatibleFunctionLpTerm (F n)))
    (hgrad : ∀ i, Summable (fun n => compatibleGradientLpTerm (F n) i)) :
    MemH10 U (compatibleSeriesLimit F hfun hgrad).toFun := by
  let f := compatibleSeriesLimit F hfun hgrad
  exact memH10_of_tendsto_H1 hU f (compatiblePartialSum F)
    (compatible_partial_sum_memH10 F hF)
    (by
      have hlim : f.memL2.toLp f.toFun =
          (∑' n, compatibleFunctionLpTerm (F n) : Lp ℝ 2 (volumeMeasureOn U)) := by
        change (Lp.memLp (∑' n, compatibleFunctionLpTerm (F n))).toLp
          (fun x => (∑' n, compatibleFunctionLpTerm (F n)) x) = _
        exact lp_toLp_self _
      have hLp : Tendsto
          (fun N => (compatiblePartialSum F N).memL2.toLp
            (compatiblePartialSum F N).toFun)
          atTop (𝓝 (f.memL2.toLp f.toFun)) := by
        simpa only [hlim] using compatible_partial_sum_function_tendsto F hfun
      have hrev := (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
          (fun N x => (compatiblePartialSum F N).toFun x)
          (fun N => (compatiblePartialSum F N).memL2)
          (fun x => f.toFun x) f.memL2).mp hLp
      exact hrev.congr (fun N => by
        change eLpNorm (fun x => (compatiblePartialSum F N).toFun x - f.toFun x)
            2 (volume.restrict U) =
          eLpNorm (fun x => f.toFun x - (compatiblePartialSum F N).toFun x)
            2 (volumeMeasureOn U)
        simpa only [volumeMeasureOn] using
          Homogenization.eLpNorm_sub_swap
            (fun x => (compatiblePartialSum F N).toFun x) (fun x => f.toFun x)) )
    (fun i => by
      have hlim : (f.gradMemL2 i).toLp (fun x => f.grad x i) =
          (∑' n, compatibleGradientLpTerm (F n) i : Lp ℝ 2 (volumeMeasureOn U)) := by
        change (Lp.memLp (∑' n, compatibleGradientLpTerm (F n) i)).toLp
          (fun x => (∑' n, compatibleGradientLpTerm (F n) i) x) = _
        exact lp_toLp_self _
      have hLp : Tendsto
          (fun N => ((compatiblePartialSum F N).gradMemL2 i).toLp
            (fun x => (compatiblePartialSum F N).grad x i))
          atTop (𝓝 (f.gradMemL2 i |>.toLp (fun x => f.grad x i))) := by
        simpa only [hlim] using compatible_partial_sum_gradient_tendsto F hgrad i
      have hrev := (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
          (fun N x => (compatiblePartialSum F N).grad x i)
          (fun N => (compatiblePartialSum F N).gradMemL2 i)
          (fun x => f.grad x i) (f.gradMemL2 i)).mp hLp
      exact hrev.congr (fun N => by
        change eLpNorm (fun x => (compatiblePartialSum F N).grad x i - f.grad x i)
            2 (volume.restrict U) =
          eLpNorm (fun x => f.grad x i - (compatiblePartialSum F N).grad x i)
            2 (volumeMeasureOn U)
        simpa only [volumeMeasureOn] using
          Homogenization.eLpNorm_sub_swap
            (fun x => (compatiblePartialSum F N).grad x i) (fun x => f.grad x i)) )

end

end ASDExplicitGamma.Inverse
