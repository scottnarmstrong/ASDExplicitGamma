module

public import ASDExplicitGamma.Native.HeatShearMoment
public import ASDExplicitGamma.Inverse.BankHistoryPhysical
public import ASDExplicitGamma.Inverse.BankLocal
public import ASDExplicitGamma.Inverse.ClippedMatrixLocal
public import ASDExplicitGamma.Model.CutoffGaussian
public import ASDExplicitGamma.Gaussian.ModelHeatTrace
public import ASDExplicitGamma.Variational.TraceDefect
public import ASDExplicitGamma.Cold.NativeGraphTraceAverage
public import ASDExplicitGamma.Cold.SquareCellMean
public import ASDExplicitGamma.Native.HeatVHEATChild
public import ASDExplicitGamma.Statements.NativeInductionState
public import ASDExplicitGamma.Inverse.AnchorAdapter
public import ASDExplicitGamma.Gaussian.ChildResponse
public import ASDExplicitGamma.Native.HeatInitialDescendants

/-! The refined depth-ten carrier for the VHEAT source rows. -/

@[expose] public section

namespace ASDExplicitGamma.Native

open MeasureTheory Homogenization Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.Whitney
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
open scoped Topology

/-- The Cartesian index of the actual depth-ten descendants. -/
abbrev nativeHeatQ3RefinedCarrierIndex : Type := Fin (3 ^ 10 * 3 ^ 10)

/-- Convert a Cartesian depth-ten index to the two-coordinate mesh label. -/
def nativeHeatQ3RefinedChildDigits
    (ij : Fin (3 ^ 10) × Fin (3 ^ 10)) : Fin 2 → Fin (3 ^ 10) :=
  ![ij.1, ij.2]

/-- The depth-ten child of the source target cell named by `ij`. -/
noncomputable def nativeHeatQ3RefinedChildCube (Q : TriadicCube 2)
    (ij : Fin (3 ^ 10) × Fin (3 ^ 10)) : TriadicCube 2 :=
  Triadic.diagMeshCell Q 10 (nativeHeatQ3RefinedChildDigits ij)

/-- The refined child indexed by a single finite Cartesian index. -/
noncomputable def nativeHeatQ3RefinedCarrierChild (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) : TriadicCube 2 :=
  nativeHeatQ3RefinedChildCube (originCube 2 (m + 10))
    (finProdFinEquiv.symm i)

/-- The carrier is the union of the closures of all depth-ten children. -/
noncomputable def nativeHeatQ3RefinedCarrierDomain (m : ℤ) : Set (Vec 2) :=
  ⋃ i : nativeHeatQ3RefinedCarrierIndex,
    closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i))

/-- The refined carrier has the explicit `9^10` child count. -/
theorem nativeHeatQ3RefinedCarrierIndex_card :
    Fintype.card nativeHeatQ3RefinedCarrierIndex = 9 ^ 10 := by
  rw [Fintype.card_fin]
  rw [← mul_pow]
  norm_num

/-- A depth-ten child has exactly the parent scale minus ten. -/
theorem nativeHeatQ3RefinedChildCube_scale (Q : TriadicCube 2)
    (ij : Fin (3 ^ 10) × Fin (3 ^ 10)) :
    (nativeHeatQ3RefinedChildCube Q ij).scale = Q.scale - (10 : ℤ) := by
  let k : Fin 2 → Fin (3 ^ 10) := nativeHeatQ3RefinedChildDigits ij
  have hfactor :
      cubeScaleFactor (Triadic.diagMeshCell Q 10 k) =
        (3 : ℝ) ^ (Q.scale - (10 : ℤ)) := by
    rw [Triadic.diagMeshCell_side, Triadic.diagMeshRadius,
      Homogenization.cubeScaleFactor]
    rw [zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
    rfl
  have hpow :
      (3 : ℝ) ^ (Triadic.diagMeshCell Q 10 k).scale =
        (3 : ℝ) ^ (Q.scale - (10 : ℤ)) := by
    simpa [Homogenization.cubeScaleFactor] using hfactor
  have hpowInjective : Function.Injective (fun n : ℤ => (3 : ℝ) ^ n) :=
    (zpow_right_strictMono₀ (a := (3 : ℝ))
      (show (1 : ℝ) < 3 by norm_num)).injective
  have hexp := hpowInjective hpow
  change (Triadic.diagMeshCell Q 10 k).scale = Q.scale - (10 : ℤ)
  exact hexp

/-- Every refined carrier child has the target scale `m`. -/
theorem nativeHeatQ3RefinedCarrierChild_scale (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    (nativeHeatQ3RefinedCarrierChild m i).scale = m := by
  rw [nativeHeatQ3RefinedCarrierChild,
    nativeHeatQ3RefinedChildCube_scale]
  simp only [originCube]
  omega

private theorem nativeHeatQ3RefinedCarrierDomain_compact (m : ℤ) :
    IsCompact (nativeHeatQ3RefinedCarrierDomain m) := by
  apply isCompact_iUnion
  intro i
  exact (isBounded_cubeSet (nativeHeatQ3RefinedCarrierChild m i)).isCompact_closure

noncomputable instance nativeHeatQ3RefinedCarrierCompact (m : ℤ) :
    CompactSpace (nativeHeatQ3RefinedCarrierDomain m) :=
  isCompact_iff_compactSpace.mp (nativeHeatQ3RefinedCarrierDomain_compact m)

/-- Each child closure embeds into the common refined carrier. -/
theorem nativeHeatQ3RefinedCarrierChild_closure_subset (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)) ⊆
      nativeHeatQ3RefinedCarrierDomain m := by
  intro x hx
  exact Set.mem_iUnion.mpr ⟨i, hx⟩

noncomputable instance nativeHeatQ3RefinedCarrierChildCompact (m : ℤ)
    (i : nativeHeatQ3RefinedCarrierIndex) :
    CompactSpace (closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i))) :=
  isCompact_iff_compactSpace.mp
    (isBounded_cubeSet (nativeHeatQ3RefinedCarrierChild m i)).isCompact_closure

/-- Restrict a carrier function to each actual child closure. -/
noncomputable def nativeHeatQ3RefinedCarrierOldMap (m : ℤ) :
    C(nativeHeatQ3RefinedCarrierDomain m, ℝ) →L[ℝ]
      (∀ i, C(closure (cubeSet (nativeHeatQ3RefinedCarrierChild m i)), ℝ)) :=
  ContinuousLinearMap.pi fun i =>
    ContinuousMap.compCLM ℝ ℝ
      ⟨fun x => ⟨x.1, nativeHeatQ3RefinedCarrierChild_closure_subset m i x.2⟩,
        continuous_subtype_val.subtype_mk _⟩

/-- The actual center of each depth-ten child, as a point of the carrier. -/
noncomputable def nativeHeatQ3RefinedCarrierCenter (m : ℤ) :
    nativeHeatQ3RefinedCarrierIndex → nativeHeatQ3RefinedCarrierDomain m :=
  fun i => ⟨cubeCenter (nativeHeatQ3RefinedCarrierChild m i),
    nativeHeatQ3RefinedCarrierChild_closure_subset m i
      (subset_closure
        (cubeCenter_mem_cubeSet (nativeHeatQ3RefinedCarrierChild m i)))⟩

/-- The refined fresh-center map retains the exact `sqrt (1+θ)` normalization. -/
noncomputable def nativeHeatQ3RefinedCarrierFreshCenterMap (m : ℤ) (θ : ℝ) :
    C(nativeHeatQ3RefinedCarrierDomain m, ℝ) →L[ℝ]
      (nativeHeatQ3RefinedCarrierIndex → ℝ) :=
  (Real.sqrt (1 + θ))⁻¹ •
    childCenterMap (nativeHeatQ3RefinedCarrierCenter m)

/-- The nine refined physical shells are the levels `m+2` through `m+10`.
At zero-based offset `n`, their corresponding refined-grid wavelength index
is `n+2`, as in `heat_refined_grid_ratios`. -/
def nativeHeatQ3RefinedCarrierPhysicalShells (m : ℤ) : Fin 9 → ℤ :=
  fun d => m + (d.val : ℤ) + 2

/-- The physical label records the same `n+2` offset used by the refined
kernel scale and overlap profiles. -/
theorem nativeHeatQ3RefinedCarrierPhysicalShells_offset (m : ℤ) (d : Fin 9) :
    nativeHeatQ3RefinedCarrierPhysicalShells m d =
      m + ((d.val + 2 : ℕ) : ℤ) := by
  simp only [nativeHeatQ3RefinedCarrierPhysicalShells, Nat.cast_add, Nat.cast_ofNat]
  ring

/-- Every physical shell label lies in the exact refined interval. -/
theorem nativeHeatQ3RefinedCarrierPhysicalShells_mem (m : ℤ) (d : Fin 9) :
    nativeHeatQ3RefinedCarrierPhysicalShells m d ∈ Set.Icc (m + 2) (m + 10) := by
  simp only [Set.mem_Icc, nativeHeatQ3RefinedCarrierPhysicalShells]
  constructor <;> omega

/-- The nine refined shell labels are pairwise distinct. -/
theorem nativeHeatQ3RefinedCarrierPhysicalShells_injective (m : ℤ) :
    Function.Injective (nativeHeatQ3RefinedCarrierPhysicalShells m) := by
  intro i j hij
  apply Fin.ext
  simp only [nativeHeatQ3RefinedCarrierPhysicalShells] at hij
  omega

end ASDExplicitGamma.Native
