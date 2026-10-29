module

public import ASDExplicitGamma.Inverse.StoppedClusterReach

/-! Almost-sure finiteness of the actual occupied components, including all block roots. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse
open SimpleGraph MeasureTheory Filter
open scoped Topology
noncomputable section

/-- The actual physical sites in the occupied component of x. -/
def clusterSites {Ω : Type*} (B : PlanarMarks Ω) (ω : Ω) (x : BlockSite) : Set BlockSite :=
  {y | ∃ hx : x ∈ markedOccupied B ω, ∃ hy : y ∈ markedOccupied B ω,
    (blockGraph.induce (markedOccupied B ω)).Reachable ⟨x,hx⟩ ⟨y,hy⟩}

/-- The source radius majorant tends to zero along the actual integer radii. -/
theorem radius_majorant_tendsto_zero :
    Tendsto (fun R : ℕ => Real.exp (-(R:ℝ)/2)) atTop (𝓝 0) := by
  have hh := tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos (-(1:ℝ)/2)).le
    (Real.exp_lt_one_iff.mpr (by norm_num : -(1:ℝ)/2 < 0))
  convert hh using 1
  funext R
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- There is zero probability of an occupied component reaching all radii.
No finite-label independence or artificial cluster-diameter premise is used. -/
theorem unbounded_cluster_null {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B : PlanarMarks Ω) (q : ℝ)
    (hB : PlanarMarkControl μ B q) (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000)
    (x : BlockSite) : μ (⋂ R : ℕ, clusterReaches B x R) = 0 := by
  have hb (R : ℕ) : μ.real (⋂ K : ℕ, clusterReaches B x K) ≤ Real.exp (-(R:ℝ)/2) :=
    (measureReal_mono (Set.iInter_subset _ R)).trans (cluster_radius_probability μ B q hB hq0 hq x R)
  have hh := ge_of_tendsto radius_majorant_tendsto_zero (Eventually.of_forall hb)
  have hz : μ.real (⋂ R : ℕ, clusterReaches B x R) = 0 := le_antisymm hh measureReal_nonneg
  exact (measureReal_eq_zero_iff (by finiteness)).mp hz

/-- Failure to reach one integer radius places the entire actual component
inside an explicitly finite physical cube. -/
theorem cluster_sites_finite_of_not_reaches {Ω : Type*} (B : PlanarMarks Ω)
    (ω : Ω) (x : BlockSite) (R : ℕ) (hR : ω ∉ clusterReaches B x R) :
    (clusterSites B ω x).Finite := by
  let a : BlockSite := fun d => x d-(R:ℤ)
  apply (blockCubeSites a (2*R+1)).finite_toSet.subset
  intro y hy
  rw [Finset.mem_coe,mem_cube_sites]
  obtain ⟨hx,hy,hr⟩ := hy
  intro d
  have hd : |y d-x d| < (R:ℤ) := by
    by_contra! hh
    exact hR ⟨hx,⟨y,hy⟩,hr,d,hh⟩
  have hb := abs_lt.mp hd
  change x d-(R:ℤ) ≤ y d ∧ y d < x d-(R:ℤ)+((2*R+1:ℕ):ℤ)
  constructor <;> omega

/-- Every actual occupied component is finite simultaneously at almost every
sample, over the entire countable planar block lattice. -/
theorem clusters_ae_finite {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B : PlanarMarks Ω) (q : ℝ)
    (hB : PlanarMarkControl μ B q) (hq0 : 0 ≤ q) (hq : q ≤ 1/10000000000) :
    ∀ᵐ ω ∂μ, ∀ x : BlockSite, (clusterSites B ω x).Finite := by
  apply ae_all_iff.mpr
  intro x
  have hn : ∀ᵐ ω ∂μ, ω ∉ ⋂ R : ℕ, clusterReaches B x R :=
    (ae_iff.mpr (by simpa only [not_not,Set.ofPred_mem_eq] using unbounded_cluster_null μ B q hB hq0 hq x))
  filter_upwards [hn] with ω hω
  have hh : ∃ R, ω ∉ clusterReaches B x R := by
    by_contra! hall
    exact hω (Set.mem_iInter.mpr hall)
  obtain ⟨R,hR⟩ := hh
  exact cluster_sites_finite_of_not_reaches B ω x R hR

end
end ASDExplicitGamma.Inverse
