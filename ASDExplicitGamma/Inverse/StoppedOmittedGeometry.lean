module

public import ASDExplicitGamma.Inverse.StoppedLocalizedAgreement
public import ASDExplicitGamma.Inverse.StoppedLocalObservationGeometry

/-! At most nine aligned cubes at each omitted label can meet the inspection box. -/
@[expose] public section
namespace ASDExplicitGamma.Inverse

/-- A width-s aligned cube intersecting a radius-N box, N<=s, differs in
index by at most one from the aligned cube containing the center. -/
theorem aligned_index_close_of_inspection (s N : ℕ) (hs : 0 < s) (hNs : N ≤ s)
    (x y : BlockSite) (hy : y ∈ blockCube (fun d => x d-(N:ℤ)) (2*N+1)) :
    ∀ d, |alignedCubeIndex s y d-alignedCubeIndex s x d| ≤ 1 := by
  intro d
  have hsZ : (0:ℤ) < s := by exact_mod_cast hs
  have hnear : x d-(s:ℤ) ≤ y d ∧ y d ≤ x d+(s:ℤ) := by
    have hd := hy d
    change x d-(N:ℤ) ≤ y d ∧ y d < x d-(N:ℤ)+((2*N+1:ℕ):ℤ) at hd
    constructor <;> omega
  have hx := mem_own_aligned_cube s hs x d
  change (s:ℤ)*(x d/(s:ℤ)) ≤ x d ∧ x d < (s:ℤ)*(x d/(s:ℤ))+(s:ℤ) at hx
  change |y d/(s:ℤ)-x d/(s:ℤ)| ≤ 1
  rw [abs_le]
  constructor
  · have hl : x d/(s:ℤ)-1 ≤ y d/(s:ℤ) := by
      apply (Int.le_ediv_iff_mul_le hsZ).mpr
      nlinarith only [hx.1,hnear.1]
    omega
  · have hu : y d/(s:ℤ) ≤ x d/(s:ℤ)+1 := by
      apply (Int.ediv_le_iff_le_mul hsZ).mpr
      nlinarith only [hx.2,hnear.2]
    omega

/-- A concrete intersecting omitted cube belongs to the exact nine-index
candidate population; the activation still retains all of its raw sites. -/
theorem intersecting_aligned_cube_mem_candidates (s N : ℕ) (hs : 0 < s) (hNs : N ≤ s)
    (x i y : BlockSite) (hy : y ∈ blockCube (fun d => x d-(N:ℤ)) (2*N+1))
    (hyi : y ∈ blockCube (alignedCubeBase s i) s) :
    i ∈ blockBox (alignedCubeIndex s x) := by
  have hi := (aligned_cube_index_iff s hs y i).mpr hyi
  rw [← hi]
  exact (mem_block_box _ _).mpr (aligned_index_close_of_inspection s N hs hNs x y hy)

/-- The actual omitted event is covered by at most nine full aligned-cube
activations at each omitted label, including the first label M+1. -/
theorem omitted_activation_subset_candidates {Ω : Type*} (B : PlanarMarks Ω)
    (M : ℕ) (x : BlockSite) :
    omittedActivation B M (3^M) x ⊆ ⋃ k : ℕ,
      ⋃ i ∈ blockBox (alignedCubeIndex (3^(M+k+1)) x), positiveActivation B (M+k) i := by
  rintro ω ⟨n,hn,i,hi,y,hy,hyi⟩
  have hs : (3^M:ℕ) ≤ 3^(n+1) := pow_le_pow_right₀ (by norm_num : (1:ℕ) ≤ 3) (by omega)
  have hc := intersecting_aligned_cube_mem_candidates (3^(n+1)) (3^M) (by positivity) hs x i y hy hyi
  apply Set.mem_iUnion.mpr
  refine ⟨n-M,?_⟩
  rw [show M+(n-M) = n by omega]
  exact Set.mem_iUnion₂.mpr ⟨i,hc,hi⟩

end ASDExplicitGamma.Inverse
