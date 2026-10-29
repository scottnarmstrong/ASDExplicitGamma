module

public import ASDExplicitGamma.Inverse.StoppedLocalizedAgreement
public import ASDExplicitGamma.Inverse.StoppedDiameterTail

/-! The actual localization escape probability from the proved full cluster radius tail. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open MeasureTheory
noncomputable section

/-- An escaping component from a radius-two neighbor reaches radius N-2. -/
theorem localization_escape_subset_radius {Ω : Type*} (B : PlanarMarks Ω)
    (N : ℕ) (hN : 2 ≤ N) (x : BlockSite) :
    localizationEscape B N x ⊆ ⋃ y ∈ diameterRoots x, clusterReaches B y (N-2) := by
  rintro ω ⟨y,hy,z,hz,hout⟩
  have hybox := (mem_cube_sites _ _ _).mp hy
  have hdist : ∃ d, ((N-2:ℕ):ℤ) ≤ |z d-y d| := by
    by_contra! hn
    apply hout
    intro d
    have hdy := hybox d
    have hdz := abs_lt.mp (hn d)
    change x d-2 ≤ y d ∧ y d < x d-2+(5:ℤ) at hdy
    change x d-(N:ℤ) ≤ z d ∧ z d < x d-(N:ℤ)+((2*N+1:ℕ):ℤ)
    constructor <;> omega
  obtain ⟨hyocc,hzocc,hr⟩ := hz
  exact Set.mem_iUnion₂.mpr ⟨y,hy,hyocc,⟨z,hzocc⟩,hr,hdist⟩

/-- The complete 25-root escape union has the conservative source
exponential budget, including the finitely many small inspection radii. -/
theorem localization_escape_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B : PlanarMarks Ω) (q : ℝ)
    (hB : PlanarMarkControl μ B q) (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000)
    (N : ℕ) (x : BlockSite) :
    μ.real (localizationEscape B N x) ≤ 75*Real.exp (-(N:ℝ)/2) := by
  by_cases hN : 2 ≤ N
  · calc
      _ ≤ μ.real (⋃ y ∈ diameterRoots x, clusterReaches B y (N-2)) :=
        measureReal_mono (localization_escape_subset_radius B N hN x) (measure_ne_top μ _)
      _ ≤ ∑ y ∈ diameterRoots x, μ.real (clusterReaches B y (N-2)) := measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _y ∈ diameterRoots x, Real.exp (-((N-2:ℕ):ℝ)/2) :=
        Finset.sum_le_sum fun y _ => cluster_radius_probability μ B q hB hq0 hq y (N-2)
      _ = 25*Real.exp (1-(N:ℝ)/2) := by
        rw [Finset.sum_const,nsmul_eq_mul,diameter_roots_card,Nat.cast_sub hN]
        norm_num only [Nat.cast_ofNat]
        congr 2
        ring
      _ ≤ _ := by
        rw [show 1-(N:ℝ)/2 = 1+(-(N:ℝ)/2) by ring,Real.exp_add]
        have hh := mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le (Real.exp_pos (-(N:ℝ)/2)).le
        nlinarith only [hh]
  · have hNs : N ≤ 1 := by omega
    have hNr : (N:ℝ) ≤ 1 := by exact_mod_cast hNs
    have hh := Real.add_one_le_exp (-(N:ℝ)/2)
    have hb : (1:ℝ) ≤ 75*Real.exp (-(N:ℝ)/2) := by linarith only [hh,hNr]
    exact measureReal_le_one.trans hb

end
end ASDExplicitGamma.Inverse
