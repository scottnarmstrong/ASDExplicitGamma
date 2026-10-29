module

public import ASDExplicitGamma.Inverse.CompatibleGluing
public import Homogenization.Sobolev.L2Ambient
public import Homogenization.Sobolev.MatchedPair.Core
public import Mathlib.MeasureTheory.Function.L2Space

/-! Countable H¹₀ gluing for disjoint finite-energy corrections. -/

@[expose] public section

namespace ASDExplicitGamma.Inverse

open Homogenization MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

open ASDExplicitGamma.Triadic ASDExplicitGamma.Variational ASDExplicitGamma.Response

local instance compatibleEnergyLpFactTwo : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

local instance compatibleEnergyFiniteMeasure (Q : TriadicCube 2) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet Q)) :=
  (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume

theorem compatible_l2_finite_pythagoras {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : ℕ → E)
    (horth : ∀ i j, i ≠ j → inner ℝ (f i) (f j) = 0) (s : Finset ℕ) :
    ‖∑ i ∈ s, f i‖ ^ 2 = ∑ i ∈ s, ‖f i‖ ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have hcross : inner ℝ (f a) (∑ i ∈ s, f i) = 0 := by
        rw [inner_sum]
        apply Finset.sum_eq_zero
        intro b hb
        exact horth a b (by
          intro hab
          subst b
          exact ha hb)
      calc
        ‖f a + ∑ i ∈ s, f i‖ ^ 2 =
            ‖f a + ∑ i ∈ s, f i‖ * ‖f a + ∑ i ∈ s, f i‖ := by ring
        _ = ‖f a‖ * ‖f a‖ + ‖∑ i ∈ s, f i‖ * ‖∑ i ∈ s, f i‖ :=
            norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hcross
        _ = ‖f a‖ ^ 2 + ‖∑ i ∈ s, f i‖ ^ 2 := by ring
        _ = ‖f a‖ ^ 2 + ∑ i ∈ s, ‖f i‖ ^ 2 := by rw [ih]

theorem compatible_l2_summable_of_orthogonal_square_norm {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : ℕ → E)
    (horth : ∀ i j, i ≠ j → inner ℝ (f i) (f j) = 0)
    (hsq : Summable (fun i => ‖f i‖ ^ 2)) : Summable f := by
  classical
  rw [summable_iff_vanishing_norm]
  intro ε hε
  obtain ⟨s, hs⟩ := (summable_iff_vanishing_norm.mp hsq) (ε ^ 2) (sq_pos_of_pos hε)
  refine ⟨s, fun t hts => ?_⟩
  have hsum_nonneg : 0 ≤ ∑ i ∈ t, ‖f i‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsum_small : ∑ i ∈ t, ‖f i‖ ^ 2 < ε ^ 2 := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hsum_nonneg] using hs t hts
  have hpyth := compatible_l2_finite_pythagoras f horth t
  nlinarith [norm_nonneg (∑ i ∈ t, f i)]

private theorem compatible_lp_inner_zero_of_ae_product_zero {U : Set (Vec 2)}
    {f g : Vec 2 → ℝ} (hf : MemScalarL2 U f) (hg : MemScalarL2 U g)
    (hzero : ∀ᵐ x ∂volumeMeasureOn U, f x = 0 ∨ g x = 0) :
    inner ℝ (hf.toLp f) (hg.toLp g) = 0 := by
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp, hzero] with x hfx hgx hz
  rcases hz with hz | hz
  · rw [hfx, hgx, Real.inner_apply, hz]
    simp
  · rw [hfx, hgx, Real.inner_apply, hz]
    simp

/-- Disjoint cell supports make scalar L² corrections orthogonal.  The support
hypotheses are allowed to hold only almost everywhere, as is natural for
zero-extended Sobolev corrections. -/
theorem compatible_function_terms_orthogonal_of_disjoint_support
    {U : Set (Vec 2)} (F : ℕ → H1Function U) (S : ℕ → Set (Vec 2))
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (hsupp : ∀ i, ∀ᵐ x ∂volumeMeasureOn U,
      (F i).toFun x ≠ 0 → x ∈ S i) :
    ∀ i j, i ≠ j →
      inner ℝ (compatibleFunctionLpTerm (F i))
        (compatibleFunctionLpTerm (F j)) = 0 := by
  intro i j hij
  have hzero : ∀ᵐ x ∂volumeMeasureOn U, (F i).toFun x = 0 ∨ (F j).toFun x = 0 := by
    filter_upwards [hsupp i, hsupp j] with x hi hj
    by_cases hix : (F i).toFun x = 0
    · exact Or.inl hix
    · right
      have hSi : x ∈ S i := hi hix
      have hnotSj : x ∉ S j := by
        intro hSj
        exact Set.disjoint_left.mp (hdisj i j hij) hSi hSj
      by_contra hjx
      exact hnotSj (hj hjx)
  change inner ℝ (((F i).memL2).toLp (F i).toFun)
      (((F j).memL2).toLp (F j).toFun) = 0
  exact compatible_lp_inner_zero_of_ae_product_zero
    (F i).memL2 (F j).memL2 hzero

/-- Disjoint cell supports make each weak-gradient coordinate orthogonal in
the parent L² space. -/
theorem compatible_gradient_terms_orthogonal_of_disjoint_support
    {U : Set (Vec 2)} (F : ℕ → H1Function U) (S : ℕ → Set (Vec 2))
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (hsupp : ∀ n k, ∀ᵐ x ∂volumeMeasureOn U,
      (F n).grad x k ≠ 0 → x ∈ S n) :
    ∀ k i j, i ≠ j →
      inner ℝ (compatibleGradientLpTerm (F i) k)
        (compatibleGradientLpTerm (F j) k) = 0 := by
  intro k i j hij
  have hzero : ∀ᵐ x ∂volumeMeasureOn U,
      (F i).grad x k = 0 ∨ (F j).grad x k = 0 := by
    filter_upwards [hsupp i k, hsupp j k] with x hi hj
    by_cases hix : (F i).grad x k = 0
    · exact Or.inl hix
    · right
      have hSi : x ∈ S i := hi hix
      have hnotSj : x ∉ S j := by
        intro hSj
        exact Set.disjoint_left.mp (hdisj i j hij) hSi hSj
      by_contra hjx
      exact hnotSj (hj hjx)
  change inner ℝ (((F i).gradMemL2 k).toLp (fun x => (F i).grad x k))
      (((F j).gradMemL2 k).toLp (fun x => (F j).grad x k)) = 0
  exact compatible_lp_inner_zero_of_ae_product_zero
    ((F i).gradMemL2 k) ((F j).gradMemL2 k) hzero

/-- Source-style finite-energy H¹₀ gluing: pairwise-disjoint cell corrections
with square-summable field and gradient energy have one parent limit.  The
construction is independent of any loading parameter. -/
theorem compatible_countable_h10_gluing_of_disjoint_energy
    {U : Set (Vec 2)} (hU : IsOpenBoundedConvexDomain U)
    (F : ℕ → H1Function U) (hF : ∀ n, MemH10 U (F n).toFun)
    (S : ℕ → Set (Vec 2))
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (hsuppFun : ∀ n, ∀ᵐ x ∂volumeMeasureOn U,
      (F n).toFun x ≠ 0 → x ∈ S n)
    (hsuppGrad : ∀ n k, ∀ᵐ x ∂volumeMeasureOn U,
      (F n).grad x k ≠ 0 → x ∈ S n)
    (hfunSq : Summable (fun n => ‖compatibleFunctionLpTerm (F n)‖ ^ 2))
    (hgradSq : ∀ k, Summable
      (fun n => ‖compatibleGradientLpTerm (F n) k‖ ^ 2)) :
    MemH10 U (compatibleSeriesLimit F
      (compatible_l2_summable_of_orthogonal_square_norm _
        (compatible_function_terms_orthogonal_of_disjoint_support F S hdisj hsuppFun)
        hfunSq)
      (fun k => compatible_l2_summable_of_orthogonal_square_norm _
        (compatible_gradient_terms_orthogonal_of_disjoint_support F S hdisj hsuppGrad k)
        (hgradSq k))).toFun := by
  exact compatible_countable_h10_gluing hU F hF
    (compatible_l2_summable_of_orthogonal_square_norm _
      (compatible_function_terms_orthogonal_of_disjoint_support F S hdisj hsuppFun)
      hfunSq)
    (fun k => compatible_l2_summable_of_orthogonal_square_norm _
      (compatible_gradient_terms_orthogonal_of_disjoint_support F S hdisj hsuppGrad k)
      (hgradSq k))

/-- Poincaré supplies the value-energy series from the two coordinate
gradient-energy series, exactly as in the finite-energy root gluing step. -/
theorem compatible_function_square_summable_of_h10_gradient_energy
    {U : Set (Vec 2)} (hU : IsOpenBoundedConvexDomain U)
    (F : ℕ → H1Function U) (hF : ∀ n, MemH10 U (F n).toFun)
    (hgradSq : ∀ k, Summable
      (fun n => ‖compatibleGradientLpTerm (F n) k‖ ^ 2)) :
    Summable (fun n => ‖compatibleFunctionLpTerm (F n)‖ ^ 2) := by
  obtain ⟨C, hC, hPoincare⟩ :=
    H10Function.exists_poincare_constant_of_isOpenBoundedConvexDomain hU
  let a : ℕ → ℝ := fun n => ‖compatibleGradientLpTerm (F n) 0‖
  let b : ℕ → ℝ := fun n => ‖compatibleGradientLpTerm (F n) 1‖
  have hbound (n : ℕ) :
      ‖compatibleFunctionLpTerm (F n)‖ ≤ C * (a n + b n) := by
    obtain ⟨u, hu⟩ := hF n
    have hvalue : compatibleFunctionLpTerm (F n) = u.toH1Function.toScalarL2 := by
      change (F n).memL2.toLp (F n).toFun =
        (u.toH1Function).memL2.toLp u.toH1Function.toFun
      apply Lp.ext
      filter_upwards [(F n).memL2.coeFn_toLp,
        u.toH1Function.memL2.coeFn_toLp] with x hleft hright
      rw [hleft, hright, hu]
    have hgradL2 (i : Fin 2) :
        compatibleGradientLpTerm (F n) i =
          u.toH1Function.gradCoordToScalarL2 i := by
      change ((F n).gradMemL2 i).toLp (fun x => (F n).grad x i) =
        u.toH1Function.gradCoordToScalarL2 i
      unfold H1Function.gradCoordToScalarL2 Homogenization.toScalarL2
      apply Lp.ext
      have hae := Homogenization.gradCoord_ae_eq_of_toFun_eq hU.isOpen
        (F n) u.toH1Function hu.symm i
      filter_upwards [(F n).gradMemL2 i |>.coeFn_toLp,
        u.toH1Function.grad_memL2 i |>.coeFn_toLp, hae] with x hleft hright hgrad
      rw [hleft, hright, hgrad]
    have hsum : u.toH1Function.gradientCoordL2NormSum = a n + b n := by
      unfold H1Function.gradientCoordL2NormSum a b
      simp only [Fin.sum_univ_two]
      rw [← hgradL2 0, ← hgradL2 1]
    calc
      ‖compatibleFunctionLpTerm (F n)‖ =
          ‖u.toH1Function.toScalarL2‖ := congrArg norm hvalue
      _ ≤ C * u.toH1Function.gradientCoordL2NormSum := hPoincare u
      _ = C * (a n + b n) := by rw [hsum]
  have hmajor : Summable (fun n => 2 * C ^ 2 * (a n ^ 2 + b n ^ 2)) := by
    have hs := (hgradSq 0).add (hgradSq 1)
    have hs' := hs.mul_left (2 * C ^ 2)
    simpa only [a, b, mul_add, mul_assoc] using hs'
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _)
    (fun n => ?_) hmajor
  have ha : 0 ≤ a n := norm_nonneg _
  have hb : 0 ≤ b n := norm_nonneg _
  have hfn : 0 ≤ ‖compatibleFunctionLpTerm (F n)‖ := norm_nonneg _
  nlinarith [hbound n, hC, sq_nonneg (a n - b n)]

/-- The source finite-energy hypothesis is only the sum of coordinate
gradient energies; Poincaré derives the value-energy series before gluing. -/
theorem compatible_countable_h10_gluing_of_disjoint_gradient_energy
    {U : Set (Vec 2)} (hU : IsOpenBoundedConvexDomain U)
    (F : ℕ → H1Function U) (hF : ∀ n, MemH10 U (F n).toFun)
    (S : ℕ → Set (Vec 2))
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (hsuppFun : ∀ n, ∀ᵐ x ∂volumeMeasureOn U,
      (F n).toFun x ≠ 0 → x ∈ S n)
    (hsuppGrad : ∀ n k, ∀ᵐ x ∂volumeMeasureOn U,
      (F n).grad x k ≠ 0 → x ∈ S n)
    (hgradSq : ∀ k, Summable
      (fun n => ‖compatibleGradientLpTerm (F n) k‖ ^ 2)) :
    MemH10 U (compatibleSeriesLimit F
      (compatible_l2_summable_of_orthogonal_square_norm _
        (compatible_function_terms_orthogonal_of_disjoint_support F S hdisj hsuppFun)
        (compatible_function_square_summable_of_h10_gradient_energy hU F hF hgradSq))
      (fun k => compatible_l2_summable_of_orthogonal_square_norm _
        (compatible_gradient_terms_orthogonal_of_disjoint_support F S hdisj hsuppGrad k)
        (hgradSq k))).toFun := by
  exact compatible_countable_h10_gluing_of_disjoint_energy hU F hF S hdisj
    hsuppFun hsuppGrad
    (compatible_function_square_summable_of_h10_gradient_energy hU F hF hgradSq)
    hgradSq

/-- The Hilbert-L² representative of one parent flux correction. -/
noncomputable def compatibleFluxHilbertTerm {U : Set (Vec 2)}
    {F : Vec 2 → Vec 2} (hF : MemVectorL2 U F) : HilbertVectorL2 U :=
  toHilbertVectorL2OfVecField hF

private theorem compatible_flux_inner_zero_of_ae_product_zero
    {U : Set (Vec 2)} {f g : Vec 2 → Vec 2}
    (hf : MemVectorL2 U f) (hg : MemVectorL2 U g)
    (hzero : ∀ᵐ x ∂volumeMeasureOn U, f x = 0 ∨ g x = 0) :
    inner ℝ (compatibleFluxHilbertTerm hf) (compatibleFluxHilbertTerm hg) = 0 := by
  change inner ℝ (toHilbertVectorL2OfVecField hf)
    (toHilbertVectorL2OfVecField hg) = 0
  rw [inner_toHilbertVectorL2OfVecField_eq_integral hf hg]
  apply integral_eq_zero_of_ae
  filter_upwards [hzero] with x hx
  rcases hx with hx | hx
  · simp [vecDot, hx]
  · simp [vecDot, hx]

/-- Disjoint supports make the zero-extended parent flux corrections
orthogonal in the actual Hilbert-vector L² space. -/
theorem compatible_flux_terms_orthogonal_of_disjoint_support
    {U : Set (Vec 2)} (F : ℕ → Vec 2 → Vec 2)
    (hF : ∀ n, MemVectorL2 U (F n)) (S : ℕ → Set (Vec 2))
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (hsupp : ∀ n, ∀ᵐ x ∂volumeMeasureOn U, F n x ≠ 0 → x ∈ S n) :
    ∀ i j, i ≠ j →
      inner ℝ (compatibleFluxHilbertTerm (hF i))
        (compatibleFluxHilbertTerm (hF j)) = 0 := by
  intro i j hij
  have hzero : ∀ᵐ x ∂volumeMeasureOn U, F i x = 0 ∨ F j x = 0 := by
    filter_upwards [hsupp i, hsupp j] with x hi hj
    by_cases hix : F i x = 0
    · exact Or.inl hix
    · right
      have hSi : x ∈ S i := hi hix
      have hnotSj : x ∉ S j := by
        intro hSj
        exact Set.disjoint_left.mp (hdisj i j hij) hSi hSj
      by_contra hjx
      exact hnotSj (hj hjx)
  exact compatible_flux_inner_zero_of_ae_product_zero (hF i) (hF j) hzero

/-- The sum of squared plain L² flux norms controls the corresponding
Hilbert-vector energy series. -/
theorem compatible_flux_hilbert_energy_summable
    {U : Set (Vec 2)} (F : ℕ → Vec 2 → Vec 2)
    (hF : ∀ n, MemVectorL2 U (F n))
    (henergy : Summable (fun n => ‖toVectorL2 (hF n)‖ ^ 2)) :
    Summable (fun n => ‖compatibleFluxHilbertTerm (hF n)‖ ^ 2) := by
  have hmajor : Summable (fun n => 4 * ‖toVectorL2 (hF n)‖ ^ 2) :=
    henergy.mul_left 4
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _)
    (fun n => ?_) hmajor
  have hnorm := norm_toHilbertVectorL2OfVecField_le (hF n)
  have hv : 0 ≤ ‖toVectorL2 (hF n)‖ := norm_nonneg _
  have ht : 0 ≤ ‖compatibleFluxHilbertTerm (hF n)‖ := norm_nonneg _
  have hsq := (sq_le_sq₀ ht (mul_nonneg (by norm_num) hv)).mpr hnorm
  have hsq' : ‖compatibleFluxHilbertTerm (hF n)‖ ^ 2 ≤
      4 * ‖toVectorL2 (hF n)‖ ^ 2 := by
    norm_num at hsq ⊢
    nlinarith
  exact hsq'

/-- The parent flux obtained by countably gluing square-summable corrections. -/
noncomputable def compatibleFluxSeriesLimit {U : Set (Vec 2)}
    (F : ℕ → Vec 2 → Vec 2) (hF : ∀ n, MemVectorL2 U (F n)) :
    HilbertVectorL2 U := ∑' n, compatibleFluxHilbertTerm (hF n)

/-- All-test zero-normal-trace solenoidality passes to the countable parent
flux limit by continuity of the L² pairing. -/
theorem compatible_flux_series_limit_solenoidal
    {U : Set (Vec 2)} (F : ℕ → Vec 2 → Vec 2)
    (hF : ∀ n, MemVectorL2 U (F n))
    (hsum : Summable (fun n => compatibleFluxHilbertTerm (hF n)))
    (hsol : ∀ n, IsSolenoidalZeroNormalTraceOn U (F n)) :
    IsSolenoidalZeroNormalTraceOn U
      (fun x => (compatibleFluxSeriesLimit F hF x).toVec) := by
  let G := compatibleFluxSeriesLimit F hF
  let V : VectorL2 U := hilbertVectorL2ToVectorL2 G
  let hV : MemVectorL2 U (fun x => V x) := MeasureTheory.Lp.memLp V
  have hVself : toVectorL2 hV = V := by
    apply Lp.ext
    exact hV.coeFn_toLp
  have hGrep : toHilbertVectorL2OfVecField hV = G := by
    calc
      toHilbertVectorL2OfVecField hV = vectorL2ToHilbertVectorL2 (toVectorL2 hV) :=
        (vectorL2ToHilbertVectorL2_toVectorL2 hV).symm
      _ = vectorL2ToHilbertVectorL2 V := by rw [hVself]
      _ = G := vectorL2ToHilbertVectorL2_hilbertVectorL2ToVectorL2 G
  intro φ
  change ∫ x in U, vecDot ((G x).toVec) (φ.grad x) ∂volume = 0
  let H : HilbertVectorL2 U :=
    toHilbertVectorL2OfVecField φ.grad_memVectorL2
  have hterm (n : ℕ) :
      inner ℝ (compatibleFluxHilbertTerm (hF n)) H = 0 := by
    change inner ℝ (toHilbertVectorL2OfVecField (hF n)) H = 0
    rw [inner_toHilbertVectorL2OfVecField_eq_integral (hF n) φ.grad_memVectorL2]
    exact hsol n φ
  have hmap := (innerSLFlip ℝ H).map_tsum hsum
  have heq : inner ℝ (∑' n, compatibleFluxHilbertTerm (hF n)) H =
        ∑' n, inner ℝ (compatibleFluxHilbertTerm (hF n)) H := by
    simpa only [innerSLFlip_apply_apply] using hmap
  have hinner : inner ℝ G H = 0 := by
    change inner ℝ (∑' n, compatibleFluxHilbertTerm (hF n)) H = 0
    rw [heq]
    calc
      _ = ∑' n, (0 : ℝ) := tsum_congr hterm
      _ = 0 := tsum_zero
  have hfield := coeFn_hilbertVectorL2ToVectorL2 (U := U) G
  have hInt :
      (∫ x in U, vecDot (V x) (φ.grad x) ∂volume) =
        ∫ x in U, vecDot ((G x).toVec) (φ.grad x) ∂volume := by
    apply integral_congr_ae
    filter_upwards [hfield] with x hx
    exact congrArg (fun v : Vec 2 => vecDot v (φ.grad x)) hx
  have hpair : inner ℝ G H =
      ∫ x in U, vecDot ((G x).toVec) (φ.grad x) ∂volume := by
    calc
      inner ℝ G H = inner ℝ (toHilbertVectorL2OfVecField hV) H := by rw [hGrep]
      _ = ∫ x in U, vecDot (V x) (φ.grad x) ∂volume :=
        inner_toHilbertVectorL2OfVecField_eq_integral hV φ.grad_memVectorL2
      _ = ∫ x in U, vecDot ((G x).toVec) (φ.grad x) ∂volume := hInt
  rw [← hpair]
  exact hinner

/-- Source-style flux gluing: pairwise-disjoint local zero-normal-trace fields
with finite total L² energy produce one admissible parent flux. -/
theorem compatible_countable_flux_gluing_of_disjoint_energy
    {U : Set (Vec 2)} (F : ℕ → Vec 2 → Vec 2)
    (hF : ∀ n, MemVectorL2 U (F n))
    (hsol : ∀ n, IsSolenoidalZeroNormalTraceOn U (F n))
    (S : ℕ → Set (Vec 2))
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (hsupp : ∀ n, ∀ᵐ x ∂volumeMeasureOn U, F n x ≠ 0 → x ∈ S n)
    (henergy : Summable (fun n => ‖toVectorL2 (hF n)‖ ^ 2)) :
    IsSolenoidalZeroNormalTraceOn U
      (fun x => (compatibleFluxSeriesLimit F hF x).toVec) := by
  exact compatible_flux_series_limit_solenoidal F hF
    (compatible_l2_summable_of_orthogonal_square_norm _
      (compatible_flux_terms_orthogonal_of_disjoint_support F hF S hdisj hsupp)
      (compatible_flux_hilbert_energy_summable F hF henergy)) hsol

/-- A parent response pair obtained by gluing disjoint local potential
corrections and zero-normal-trace flux corrections.  The two positive energy
series are the only summability inputs; the output is one H¹₀ potential and
one admissible solenoidal L² flux on the parent. -/
theorem compatible_countable_response_gluing_of_disjoint_energy
    {U : Set (Vec 2)} (hU : IsOpenBoundedConvexDomain U)
    (F : ℕ → H1Function U) (hF : ∀ n, MemH10 U (F n).toFun)
    (G : ℕ → Vec 2 → Vec 2) (hG : ∀ n, MemVectorL2 U (G n))
    (hsol : ∀ n, IsSolenoidalZeroNormalTraceOn U (G n))
    (S : ℕ → Set (Vec 2))
    (hdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (hFfun : ∀ n, ∀ᵐ x ∂volumeMeasureOn U,
      (F n).toFun x ≠ 0 → x ∈ S n)
    (hFgrad : ∀ n k, ∀ᵐ x ∂volumeMeasureOn U,
      (F n).grad x k ≠ 0 → x ∈ S n)
    (hGsupp : ∀ n, ∀ᵐ x ∂volumeMeasureOn U,
      G n x ≠ 0 → x ∈ S n)
    (hFenergy : ∀ k, Summable
      (fun n => ‖compatibleGradientLpTerm (F n) k‖ ^ 2))
    (hGenergy : Summable (fun n => ‖toVectorL2 (hG n)‖ ^ 2)) :
    MemH10 U (compatibleSeriesLimit F
      (compatible_l2_summable_of_orthogonal_square_norm _
        (compatible_function_terms_orthogonal_of_disjoint_support F S hdisj hFfun)
        (compatible_function_square_summable_of_h10_gradient_energy hU F hF hFenergy))
      (fun k => compatible_l2_summable_of_orthogonal_square_norm _
        (compatible_gradient_terms_orthogonal_of_disjoint_support F S hdisj hFgrad k)
        (hFenergy k))).toFun ∧
    IsSolenoidalZeroNormalTraceOn U
      (fun x => (compatibleFluxSeriesLimit G hG x).toVec) := by
  constructor
  · exact compatible_countable_h10_gluing_of_disjoint_gradient_energy
      hU F hF S hdisj hFfun hFgrad hFenergy
  · exact compatible_countable_flux_gluing_of_disjoint_energy
      G hG hsol S hdisj hGsupp hGenergy

/-- One loading-independent interpolant handles actual adjacent Whitney mesh
depths, supplies the source variational response lift, and accompanies the
countable finite-energy potential/flux glue on the same parent cube. -/
theorem exists_adjacent_whitney_compatible_parent_response
    {ι : Type*} [Fintype ι] (Q : TriadicCube 2) (H k : ℕ)
    (layer : ι → ℕ) (hlayer : ∀ a, layer a = k ∨ layer a = k + 1)
    (components : ∀ a,
      Finset (InteriorNode (compatibleWhitneyMeshDepth H (layer a))))
    (hne : ∀ a, (components a).Nonempty)
    (hdisj : ∀ a b, a ≠ b →
      Disjoint
        (refineComponent (compatibleWhitneyMeshDepth H (k + 1))
          (fun a => compatibleWhitneyMeshDepth H (layer a))
          (by
            intro a
            rcases hlayer a with ha | ha
            · rw [ha]
              unfold compatibleWhitneyMeshDepth whitneyProfile
              omega
            · rw [ha])
          components a)
        (refineComponent (compatibleWhitneyMeshDepth H (k + 1))
          (fun a => compatibleWhitneyMeshDepth H (layer a))
          (by
            intro a
            rcases hlayer a with ha | ha
            · rw [ha]
              unfold compatibleWhitneyMeshDepth whitneyProfile
              omega
            · rw [ha])
          components b))
    (hU : IsOpenBoundedConvexDomain (openCubeSet Q))
    (F : ℕ → H1Function (openCubeSet Q))
    (hF : ∀ n, MemH10 (openCubeSet Q) (F n).toFun)
    (G : ℕ → Vec 2 → Vec 2) (hG : ∀ n, MemVectorL2 (openCubeSet Q) (G n))
    (hsol : ∀ n, IsSolenoidalZeroNormalTraceOn (openCubeSet Q) (G n))
    (S : ℕ → Set (Vec 2))
    (hSdisj : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (hFfun : ∀ n, ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q),
      (F n).toFun x ≠ 0 → x ∈ S n)
    (hFgrad : ∀ n i, ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q),
      (F n).grad x i ≠ 0 → x ∈ S n)
    (hGsupp : ∀ n, ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q),
      G n x ≠ 0 → x ∈ S n)
    (hFenergy : ∀ i, Summable
      (fun n => ‖compatibleGradientLpTerm (F n) i‖ ^ 2))
    (hGenergy : Summable (fun n => ‖toVectorL2 (hG n)‖ ^ 2)) :
    ∃ I : H1Function (openCubeSet Q) →ₗ[ℝ] H1Function (openCubeSet Q),
      (∀ a b,
        compatibleWhitneyMeshDepth H (layer a) ≤
            compatibleWhitneyMeshDepth H (layer b) + 2 ∧
        compatibleWhitneyMeshDepth H (layer b) ≤
            compatibleWhitneyMeshDepth H (layer a) + 2) ∧
      (∀ a z, z ∈ components a → ∀ p (r : H10Function (openCubeSet Q)),
        (I (ASDExplicitGamma.Variational.lemmaVAffinePotential
          (isOpenBoundedConvexDomain_openCubeSet Q) p r)).toFun
          (diagInteriorVertex Q (compatibleWhitneyMeshDepth H (layer a)) z) =
          ∑ i : Fin 2, p i *
            componentMidpoint Q (compatibleWhitneyMeshDepth H (layer a))
              (components a) (hne a) i) ∧
      (∀ p (r : H10Function (openCubeSet Q)),
        MemH10 (openCubeSet Q)
          (ASDExplicitGamma.Variational.lemmaVAffinePotential
            (isOpenBoundedConvexDomain_openCubeSet Q) p r -
            I (ASDExplicitGamma.Variational.lemmaVAffinePotential
              (isOpenBoundedConvexDomain_openCubeSet Q) p r)).toFun) ∧
      (∀ p (r : H10Function (openCubeSet Q)) (η w : H1Function (openCubeSet Q)),
        (hη : MemLp η.toFun (⊤ : ENNReal) (volume.restrict (openCubeSet Q))) →
        (hDη : ∀ i, MemLp (fun x => η.grad x i) (⊤ : ENNReal)
          (volume.restrict (openCubeSet Q))) →
        let UQ := openCubeSet Q
        let hUQ := isOpenBoundedConvexDomain_openCubeSet Q
        let v := ASDExplicitGamma.Variational.lemmaVAffinePotential hUQ p r
        MemVectorL2 UQ (localizedColumnProductDivergence η (v-I v)) ∧
        IsSolenoidalZeroNormalTraceOn UQ (localizedColumnProductDivergence η (v-I v)) ∧
        (∀ x, localizedColumnProductDivergence η (v-I v) x =
          (v-I v).toFun x • lemmaVPlanarWeakColumnDivergence η x -
            η.toFun x • matVecMul responsePlanarJ ((v-I v).grad x)) ∧
        volumeAverage UQ (fun x => vecDot
          (η.toFun x • matVecMul responsePlanarJ (v.grad x)) (w.grad x)) =
        volumeAverage UQ (fun x => vecDot (lemmaVPlanarRowField I η v x) (w.grad x))) ∧
      MemH10 (openCubeSet Q) (compatibleSeriesLimit F
        (compatible_l2_summable_of_orthogonal_square_norm _
          (compatible_function_terms_orthogonal_of_disjoint_support F S hSdisj hFfun)
          (compatible_function_square_summable_of_h10_gradient_energy hU F hF hFenergy))
        (fun i => compatible_l2_summable_of_orthogonal_square_norm _
          (compatible_gradient_terms_orthogonal_of_disjoint_support F S hSdisj hFgrad i)
          (hFenergy i))).toFun ∧
      IsSolenoidalZeroNormalTraceOn (openCubeSet Q)
        (fun x => (compatibleFluxSeriesLimit G hG x).toVec) := by
  obtain ⟨I, hnodes, hresidual, hlift⟩ :=
    exists_adjacent_whitney_compatible_parent_interpolant
      Q H k layer hlayer components hne hdisj
  have hdepthMismatch : ∀ a b,
      compatibleWhitneyMeshDepth H (layer a) ≤
          compatibleWhitneyMeshDepth H (layer b) + 2 ∧
      compatibleWhitneyMeshDepth H (layer b) ≤
          compatibleWhitneyMeshDepth H (layer a) + 2 := by
    intro a b
    rcases hlayer a with ha | ha <;> rcases hlayer b with hb | hb
    · rw [ha, hb]
      omega
    · rw [ha, hb]
      have hgap := compatible_whitney_adjacent_mesh_depths H k
      omega
    · rw [ha, hb]
      have hgap := compatible_whitney_adjacent_mesh_depths H k
      omega
    · rw [ha, hb]
      omega
  have hglue := compatible_countable_response_gluing_of_disjoint_energy
    hU F hF G hG hsol S hSdisj hFfun hFgrad hGsupp hFenergy hGenergy
  exact ⟨I, hdepthMismatch, hnodes, hresidual, hlift, hglue.1, hglue.2⟩

end

end ASDExplicitGamma.Inverse
