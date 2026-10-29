module

public import ASDExplicitGamma.Scalar.PhysicalResolventParity
public import ASDExplicitGamma.Scalar.FlatSourceQ3ActualBank
public import ASDExplicitGamma.Scalar.FlatResolvent
public import ASDExplicitGamma.Scalar.FlatResolventModes
public import ASDExplicitGamma.Scalar.FlatWickAdmissible
public import ASDExplicitGamma.Scalar.FlatSourceQ3ActualL128
public import ASDExplicitGamma.Scalar.FlatSourceQ3PositiveHaar
public import ASDExplicitGamma.Triadic.VectorHaarSymmetry
public import ASDExplicitGamma.Scalar.ResolventCombine
public import ASDExplicitGamma.Inverse.BridgeObserverRoots
public import ASDExplicitGamma.Inverse.PureFluxGeneratorBankLaw
public import ASDExplicitGamma.Variational.ProjectedSource
public import ASDExplicitGamma.Variational.ForcedSource
public import ASDExplicitGamma.Variational.LocalizedEnergyBounds

/-! Actual source/history, bank, and physical normalization bridge for the
flat NEW-resolvent diagonal. This module depends on the base statement and
the source-side admissibility and exact unprojected energy identity. -/

@[expose] public section

namespace ASDExplicitGamma.Scalar

open MeasureTheory Homogenization ASDExplicitGamma.Gaussian ASDExplicitGamma.Triadic
  ASDExplicitGamma.Response ASDExplicitGamma.Model ASDExplicitGamma.Inverse
  ASDExplicitGamma.Variational
open Algsuperdiff.Section3
open scoped InnerProduct InnerProductSpace

attribute [local irreducible] Homogenization.descendantsAtDepth

noncomputable section

private theorem actual_rotated_wick_hilbert_eq
    (Q : TriadicCube 2) (W : HilbertVectorL2 (openCubeSet Q))
    (hF : MeasureTheory.MemLp
      (fun x => planarQuarterTurn
        (hilbertVectorL2ToVectorL2 (U := openCubeSet Q) W x))
      2 (normalizedCubeMeasure Q)) :
    toHilbertVectorL2OfVecField
      (memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure Q hF) =
        rotateVectorL2 Q W := by
  let U := openCubeSet Q
  let F : Vec 2 → Vec 2 := fun x => planarQuarterTurn
    (hilbertVectorL2ToVectorL2 (U := U) W x)
  let fLp := hilbertVectorL2ToVectorL2 (rotateVectorL2 Q W)
  have hJ (v : Vec 2) : matVecMul responsePlanarJ v = planarQuarterTurn v := by
    funext i
    fin_cases i <;>
      simp [matVecMul, responsePlanarJ, planarQuarterTurn, Fin.sum_univ_two]
  have hfield : fLp =ᵐ[volumeMeasureOn U] F := by
    have hrotate := rotate_vectorL2_toPlain_ae Q W
    filter_upwards [hrotate] with x hx
    rw [hx]
    exact hJ _
  let hFvec := memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure Q hF
  have hfLp : MemVectorL2 U (fun x => fLp x) := by
    change MeasureTheory.MemLp fLp 2 (volumeMeasureOn U)
    exact MeasureTheory.Lp.memLp fLp
  have hfLpEq : toVectorL2 hfLp = fLp := by
    calc
      toVectorL2 hfLp = toVectorL2 (MeasureTheory.Lp.memLp fLp) := by
        apply (toVectorL2_eq_toVectorL2_iff hfLp
          (MeasureTheory.Lp.memLp fLp)).2
        filter_upwards [] with x
        rfl
      _ = fLp := MeasureTheory.Lp.toLp_coeFn fLp (MeasureTheory.Lp.memLp fLp)
  have hFfieldEq : toVectorL2 hFvec = fLp := by
    calc
      toVectorL2 hFvec = toVectorL2 hfLp := by
        apply (toVectorL2_eq_toVectorL2_iff hFvec hfLp).2
        filter_upwards [hfield] with x hx
        exact hx.symm
      _ = fLp := hfLpEq
  calc
    toHilbertVectorL2OfVecField hFvec =
        vectorL2ToHilbertVectorL2 (toVectorL2 hFvec) :=
          (vectorL2ToHilbertVectorL2_toVectorL2 hFvec).symm
    _ = vectorL2ToHilbertVectorL2 fLp := by rw [hFfieldEq]
    _ = rotateVectorL2 Q W :=
      vectorL2ToHilbertVectorL2_hilbertVectorL2ToVectorL2 _

/-- The literal fresh-shell insertion on the flat potential is the flux
projection of the admissible rotated Wick field. This connects the
source-derived H10 potential to the exact Hilbert field used by the projected
source estimate, while retaining the physical projection. -/
theorem actual_flat_source_insertion_eq_projected_wick_field
    (Q : TriadicCube 2) {a₀ b₀ c₀ d₀ : ℝ}
    (hab : a₀ < b₀) (hcd : c₀ < d₀)
    (hQ : openCubeSet Q ⊆ openRectangle a₀ b₀ c₀ d₀)
    (M : ABKModel 2) (h : ℝ) (m : ℤ)
    (ω : Cutoff.CutoffSample 2) (e : Vec 2) :
    let U := openCubeSet Q
    let K := closedRectangle a₀ b₀ c₀ d₀
    let hQcl : closure U ⊆ K := by
      change closure (openCubeSet Q) ⊆ closedRectangle a₀ b₀ c₀ d₀
      rw [← rectangle_closure a₀ b₀ c₀ d₀ hab hcd]
      exact closure_mono hQ
    let σ : ℝ := Annealed.sigmaBar M m
    let hσ : 0 < σ := (Annealed.sigmaBar M m).property
    let z := shellFieldScalarRestriction K (ω.1 (m + 1))
    let p := flatSourcePotentialCarrier Q hab hcd e z
    let W := flatSourceQ3ActualWickRepresentative Q hab hcd e (m + 1) ω
    let Fflat := fun x => planarQuarterTurn
      (hilbertVectorL2ToVectorL2 (U := U) W x)
    let hF : MeasureTheory.MemLp Fflat 2 (normalizedCubeMeasure Q) :=
      (flat_source_q3_actual_rotated_wick_admissible
        Q hab hcd hQ e m ω).1
    let Flux := (physicalFluxSpace Q).toSubmodule
    physicalProjectedInsertion Q σ hσ
      (physicalResponseRestriction Q hQcl z) (σ • p) =
      Flux.subtypeL (Flux.orthogonalProjectionOnto
        (toHilbertVectorL2OfVecField
          (memVectorL2_openCubeSet_of_memLp_normalizedCubeMeasure Q hF))) := by
  classical
  let U := openCubeSet Q
  let K := closedRectangle a₀ b₀ c₀ d₀
  have hQcl : closure U ⊆ K := by
    change closure (openCubeSet Q) ⊆ closedRectangle a₀ b₀ c₀ d₀
    rw [← rectangle_closure a₀ b₀ c₀ d₀ hab hcd]
    exact closure_mono hQ
  let σ : ℝ := Annealed.sigmaBar M m
  have hσ : 0 < σ := (Annealed.sigmaBar M m).property
  let z := shellFieldScalarRestriction K (ω.1 (m + 1))
  let p := flatSourcePotentialCarrier Q hab hcd e z
  let W := flatSourceQ3ActualWickRepresentative Q hab hcd e (m + 1) ω
  let Fflat : Vec 2 → Vec 2 := fun x => planarQuarterTurn
    (hilbertVectorL2ToVectorL2 (U := U) W x)
  have hF : MeasureTheory.MemLp Fflat 2 (normalizedCubeMeasure Q) := by
    simpa [Fflat, W] using
      (flat_source_q3_actual_rotated_wick_admissible
        Q hab hcd hQ e m ω).1
  have hW := actual_rotated_wick_hilbert_eq Q W hF
  have hsource := actual_parity_flat_insertion_eq_flux_projection_of_wick
    Q hab hcd hQ M h m ω e
  change physicalProjectedInsertion Q σ hσ
      (physicalResponseRestriction Q hQcl z) (σ • p) = _
  rw [hW]
  simpa [U, K, hQcl, σ, hσ, z, p, W] using hsource

end
end ASDExplicitGamma.Scalar
