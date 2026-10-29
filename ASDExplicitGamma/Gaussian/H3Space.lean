module

public import Homogenization.Sobolev.H1.BasicLemmas
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Subspace

@[expose] public section

open MeasureTheory Homogenization Set
open scoped Topology RealInnerProductSpace

namespace ASDExplicitGamma.Gaussian

/-- The ten ordinary two-dimensional multi-indices through order three. -/
abbrev H3Index := {a : Fin 4 × Fin 4 // a.1.val + a.2.val ≤ 3}

abbrev H3Jet (U : Set (Vec 2)) :=
  PiLp 2 (fun _ : H3Index => Lp ℝ 2 (volume.restrict U))

/-- Smooth tests supported inside the source square. -/
abbrev H3Test (U : Set (Vec 2)) :=
  {φ : Vec 2 → ℝ // ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U}

noncomputable def h3TestValue (U : Set (Vec 2)) (φ : H3Test U) : Lp ℝ 2 (volume.restrict U) :=
  (φ.2.1.continuous.memLp_of_hasCompactSupport φ.2.2.1).toLp φ.1

noncomputable def h3TestPartial (U : Set (Vec 2)) (i : Fin 2) (φ : H3Test U) :
    Lp ℝ 2 (volume.restrict U) :=
  (((φ.2.1.continuous_fderiv (by norm_num)).clm_apply continuous_const).memLp_of_hasCompactSupport
    (φ.2.2.1.fderiv_apply ℝ (basisVec i))).toLp (fun x => fderiv ℝ φ.1 x (basisVec i))

def h3Next (a : H3Index) (i : Fin 2) (ha : a.1.1.val + a.1.2.val ≤ 2) : H3Index :=
  if i = 0 then ⟨(⟨a.1.1.val + 1, by omega⟩, a.1.2), by change a.1.1.val + 1 + a.1.2.val ≤ 3; omega⟩
  else ⟨(a.1.1, ⟨a.1.2.val + 1, by omega⟩), by change a.1.1.val + (a.1.2.val + 1) ≤ 3; omega⟩

/-- The weak derivative identity is the kernel of a bounded functional on jets. -/
noncomputable def h3TestMap (U : Set (Vec 2)) (a : H3Index) (i : Fin 2)
    (ha : a.1.1.val + a.1.2.val ≤ 2) (φ : H3Test U) : H3Jet U →L[ℝ] ℝ :=
  (innerSL ℝ (h3TestPartial U i φ)).comp (PiLp.proj 2 _ a) +
    (innerSL ℝ (h3TestValue U φ)).comp (PiLp.proj 2 _ (h3Next a i ha))

/-- The ordinary weak-derivative H³ space, as compatible L² jets. -/
noncomputable def h3Space (U : Set (Vec 2)) : Submodule ℝ (H3Jet U) :=
  ⨅ a : H3Index, ⨅ i : Fin 2, ⨅ ha : a.1.1.val + a.1.2.val ≤ 2,
    ⨅ φ : H3Test U, (h3TestMap U a i ha φ).ker

theorem h3Space_isClosed (U : Set (Vec 2)) : IsClosed (h3Space U : Set (H3Jet U)) := by
  simp only [h3Space, Submodule.coe_iInf]
  exact isClosed_iInter fun a => isClosed_iInter fun i => isClosed_iInter fun ha =>
    isClosed_iInter fun φ => (h3TestMap U a i ha φ).isClosed_ker

/-- This uses exactly the source sum of the ten ordinary squared L² derivative norms. -/
theorem h3Jet_norm_sq (U : Set (Vec 2)) (u : H3Jet U) :
    ‖u‖ ^ 2 = ∑ a : H3Index, ‖u a‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
  simp only [real_inner_self_eq_norm_sq]

noncomputable instance instH3CompleteSpace (U : Set (Vec 2)) : CompleteSpace (h3Space U) :=
  (h3Space_isClosed U).completeSpace_coe

/-- Membership is exactly the weak partial derivative compatibility of the L² coordinates. -/
theorem mem_h3Space_iff (U : Set (Vec 2)) (u : H3Jet U) :
    u ∈ h3Space U ↔ ∀ (a : H3Index) (i : Fin 2)
      (ha : a.1.1.val + a.1.2.val ≤ 2),
      HasWeakPartialDerivOn U i (u a) (u (h3Next a i ha)) := by
  have ht (a : H3Index) (i : Fin 2) (ha : a.1.1.val + a.1.2.val ≤ 2)
      (φ : H3Test U) :
      h3TestMap U a i ha φ u =
        (∫ x in U, u a x * fderiv ℝ φ.1 x (basisVec i)) +
        (∫ x in U, u (h3Next a i ha) x * φ.1 x) := by
    dsimp only [h3TestMap]
    simp only [add_apply, ContinuousLinearMap.comp_apply, PiLp.proj, PiLp.projₗ,
      innerSL_apply_apply, L2.inner_def,
      RCLike.inner_apply, starRingEnd_apply, star_trivial]
    congr 1
    · apply integral_congr_ae
      have he := (φ.2.1.continuous_fderiv (by norm_num) |>.clm_apply continuous_const).memLp_of_hasCompactSupport (p := 2) (μ := volume.restrict U)
        (φ.2.2.1.fderiv_apply ℝ (basisVec i)) |>.coeFn_toLp
      filter_upwards [he] with x hx
      rw [show h3TestPartial U i φ x = fderiv ℝ φ.1 x (basisVec i) from hx]
      rfl
    · apply integral_congr_ae
      have he := φ.2.1.continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume.restrict U) φ.2.2.1 |>.coeFn_toLp
      filter_upwards [he] with x hx
      rw [show h3TestValue U φ x = φ.1 x from hx]
      rfl
  simp only [h3Space, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro hu a i ha φ hφ hcomp hsub
    have hh := hu a i ha ⟨φ, hφ, hcomp, hsub⟩
    change h3TestMap U a i ha ⟨φ, hφ, hcomp, hsub⟩ u = 0 at hh
    rw [ht] at hh
    linarith only [hh]
  · intro hu a i ha φ
    change h3TestMap U a i ha φ u = 0
    rw [ht]
    have hh := hu a i ha φ.1 φ.2.1 φ.2.2.1 φ.2.2.2
    linarith only [hh]

def h3Zero : H3Index := ⟨(0, 0), by norm_num⟩

/-- Base value of the weak Sobolev jet, as an L² class. -/
noncomputable def h3Value (U : Set (Vec 2)) : h3Space U →L[ℝ] Lp ℝ 2 (volume.restrict U) :=
  (PiLp.proj 2 _ h3Zero).comp (h3Space U).subtypeL

/-- Weak-derivative uniqueness propagates equality of one coordinate to its successors. -/
theorem h3_coord_eq_next {U : Set (Vec 2)} (hU : IsOpen U) (u v : h3Space U)
    (a : H3Index) (i : Fin 2) (ha : a.1.1.val + a.1.2.val ≤ 2)
    (he : u.1 a = v.1 a) : u.1 (h3Next a i ha) = v.1 (h3Next a i ha) := by
  have hu := (mem_h3Space_iff U u.1).mp u.2 a i ha
  have hv := (mem_h3Space_iff U v.1).mp v.2 a i ha
  rw [he] at hu
  apply Lp.ext
  exact HasWeakPartialDerivOn.ae_eq hU
    (locallyIntegrableOn_of_locallyIntegrable_restrict ((Lp.memLp _).locallyIntegrable (by norm_num)))
    (locallyIntegrableOn_of_locallyIntegrable_restrict ((Lp.memLp _).locallyIntegrable (by norm_num))) hu hv

/-- On the source open square the function determines its entire weak Sobolev jet. -/
theorem h3Value_injective {U : Set (Vec 2)} (hU : IsOpen U) : Function.Injective (h3Value U) := by
  intro u v huv
  have hz : u.1 h3Zero = v.1 h3Zero := huv
  have hall : ∀ n : ℕ, ∀ a : H3Index, a.1.1.val + a.1.2.val = n → u.1 a = v.1 a := by
    intro n
    induction n with
    | zero =>
      intro a ha
      have he : a = h3Zero := by
        apply Subtype.ext
        apply Prod.ext <;> apply Fin.ext <;> dsimp [h3Zero] <;> omega
      simpa only [he] using hz
    | succ n ih =>
      intro a ha
      by_cases h : 0 < a.1.1.val
      · let b : H3Index := ⟨(⟨a.1.1.val - 1, by omega⟩, a.1.2), by
          change a.1.1.val - 1 + a.1.2.val ≤ 3
          omega⟩
        have hb : b.1.1.val + b.1.2.val = n := by dsimp [b]; omega
        have hb2 : b.1.1.val + b.1.2.val ≤ 2 := by
          have hh := a.2
          dsimp [b]
          omega
        have he : h3Next b 0 hb2 = a := by
          simp only [h3Next]
          apply Subtype.ext
          apply Prod.ext <;> apply Fin.ext <;> dsimp [b]
          omega
        simpa only [he] using h3_coord_eq_next hU u v b 0 hb2 (ih b hb)
      · let b : H3Index := ⟨(a.1.1, ⟨a.1.2.val - 1, by omega⟩), by
          change a.1.1.val + (a.1.2.val - 1) ≤ 3
          omega⟩
        have hb : b.1.1.val + b.1.2.val = n := by dsimp [b]; omega
        have hb2 : b.1.1.val + b.1.2.val ≤ 2 := by
          have hh := a.2
          dsimp [b]
          omega
        have he : h3Next b 1 hb2 = a := by
          simp only [h3Next, show (1 : Fin 2) ≠ 0 by decide, ite_false]
          apply Subtype.ext
          apply Prod.ext <;> apply Fin.ext <;> dsimp [b]
          omega
        simpa only [he] using h3_coord_eq_next hU u v b 1 hb2 (ih b hb)
  apply Subtype.ext
  exact PiLp.ext fun a => hall _ a rfl

end ASDExplicitGamma.Gaussian
