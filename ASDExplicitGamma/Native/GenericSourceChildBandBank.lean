module

public import ASDExplicitGamma.Native.GenericSourceChildBandFrame
public import ASDExplicitGamma.Inverse.FullResponseCoefficientTransport
public import ASDExplicitGamma.Inverse.BankObservers
public import ASDExplicitGamma.Model.Cutoff
public import ASDExplicitGamma.Inverse.PureFluxGeneratorBankLaw
public import ASDExplicitGamma.Inverse.BankOnePassMeanActual
public import ASDExplicitGamma.Gaussian.ShellBracket

/-! The actual local and full128 banks along simultaneous source-band heat. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory Algsuperdiff.Section3 ASDExplicitGamma.Gaussian
open ASDExplicitGamma.Inverse ASDExplicitGamma.Triadic ASDExplicitGamma.Response
open ASDExplicitGamma.Variational
open scoped ENNReal
noncomputable section

/-- Actual extended local inverse history on the simultaneous finite band. -/
def nativeSourceChildBandHistory (M : ABKModel 2) (n : ℤ) (height : ℕ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) : ℝ≥0∞ :=
  bankFiniteRootHistoryMax (bankLocalRoots (originCube 2 (n-1)) 4) M n (n+(height:ℤ))
    (fun _ => Real.sqrt t) ω

/-- The genuine local positive remainder on that same source-band law. -/
def nativeSourceChildBandRemainder (M : ABKModel 2) (n : ℤ) (height : ℕ) (t : ℝ) :
    Cutoff.CutoffSample 2 → ℝ :=
  inverseBankPopulationRemainder .localInverse (bankLocalRoots (originCube 2 (n-1)) 4)
    M n (n+(height:ℤ)) (fun _ => Real.sqrt t)

private theorem source_child_bank_geometry (Q : TriadicCube 2) (n : ℤ) (rmax : ℕ)
    (hrmax : rmax ≤ 4)
    (hscale : Q.scale=n-1) :
    (∀ U ∈ bankLocalRoots Q rmax, U.scale ≤ n ∧ n-U.scale ≤ 5) ∧
      (bankLocalRoots Q rmax).card ≤ 6*9^45 := by
  classical
  refine ⟨?_,(bank_local_roots_geometry Q rmax (by omega)).2⟩
  intro U hU
  rw [bankLocalRoots] at hU
  simp only [Finset.mem_insert] at hU
  rcases hU with hself | hU
  · rw [hself,hscale]
    omega
  simp only [Finset.mem_biUnion] at hU
  obtain ⟨r,hr,hU⟩ := hU
  have hs := scale_eq_sub_of_mem_descendantsAtDepth hU
  have hrr := Finset.mem_range.mp hr
  rw [hscale] at hs
  omega

/-- The child observation cube and its four source refinement layers lie
within five generations of the completed old field cutoff. -/
theorem native_source_child_bank_geometry (n : ℤ) :
    (∀ U ∈ bankLocalRoots (originCube 2 (n-1)) 4, U.scale ≤ n ∧ n-U.scale ≤ 5) ∧
      (bankLocalRoots (originCube 2 (n-1)) 4).card ≤ 6*9^45 :=
  source_child_bank_geometry (originCube 2 (n-1)) n 4 le_rfl rfl

/-- All local-bank estimates, including the small positive reserve and
extended history finiteness, hold on every simultaneous source-band law. -/
theorem native_source_child_band_local_bank
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (height : ℕ)
    (hpast : ∀ j < n, nativeInductionState M h j) (t : ℝ) (ht1 : t ≤ 1) :
    InverseBankConclusion M .localInverse (bankLocalRoots (originCube 2 (n-1)) 4)
      n (n+(height:ℤ)) (fun _ => Real.sqrt t) := by
  have hgeom := native_source_child_bank_geometry n
  have hmean := (bank_inverse_mean_inputs_of_states M h hM hg n hpast).2
  exact local_inverse_bank M h hM hg _ n (n+(height:ℤ)) (by omega) _
    (fun _ _ => ⟨Real.sqrt_nonneg t,Real.sqrt_le_one.mpr ht1⟩)
    hgeom.1 hgeom.2 hpast hmean

/-- The actual local source history has a finite positive split, with the
same OLD `b` and genuine `3e-46` remainder as the sequential source path. -/
theorem native_source_child_band_history_rare_split
    (M : ABKModel 2) (h : ℝ) (hM : PlanarQ3Gaussian M h)
    (hg : M.gamma ≤ gammaZero) (n : ℤ) (height : ℕ)
    (hpast : ∀ j < n, nativeInductionState M h j) (t : ℝ) (ht1 : t ≤ 1) :
    (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure, nativeSourceChildBandHistory M n height t ω < ⊤) ∧
    Measurable (nativeSourceChildBandRemainder M n height t) ∧
    (∀ ω, 0 ≤ nativeSourceChildBandRemainder M n height t ω) ∧
    eLpNorm (nativeSourceChildBandRemainder M n height t) 128 (Cutoff.cutoffSampleLaw M).toMeasure ≤
      ENNReal.ofReal (3/10^46:ℝ) ∧
    (∀ᵐ ω ∂(Cutoff.cutoffSampleLaw M).toMeasure,
      (nativeSourceChildBandHistory M n height t ω).toReal ≤
        (3683/2500:ℝ)+nativeSourceChildBandRemainder M n height t ω) := by
  have hb := native_source_child_band_local_bank M h hM hg n height hpast t ht1
  refine ⟨hb.history_finite,hb.remainder_measurable,hb.remainder_nonneg,?_,?_⟩
  · simpa only [nativeSourceChildBandRemainder,inverseBankReserve,
      Rat.cast_div,Rat.cast_ofNat,Rat.cast_pow] using hb.remainder_L128
  · filter_upwards [hb.history_le] with ω hω
    have hR := hb.remainder_nonneg ω
    have hcap : (0:ℝ) ≤ (inverseBankCap .localInverse:ℝ) := by norm_num [inverseBankCap]
    rw [←ENNReal.ofReal_add hcap hR] at hω
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hω
    rw [ENNReal.toReal_ofReal (add_nonneg hcap hR)] at hh
    simpa only [nativeSourceChildBandHistory,nativeSourceChildBandRemainder,inverseBankCap,
      Rat.cast_div,Rat.cast_ofNat] using hh


end
end ASDExplicitGamma.Native
