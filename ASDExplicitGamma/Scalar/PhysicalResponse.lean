module

public import ASDExplicitGamma.Gaussian.ModelHeatLaw
public import ASDExplicitGamma.Response.Analytic

/-! Bind the model's actual OLD coefficient and partial fresh-shell insertion
to the response observable on a physical square. -/

@[expose] public section

open MeasureTheory Homogenization
open ASDExplicitGamma.Gaussian ASDExplicitGamma.Model ASDExplicitGamma.Response
open Algsuperdiff.Frozen.Assumptions Algsuperdiff.Section3
open scoped Topology

namespace ASDExplicitGamma.Scalar

local instance physicalResponseCompactSquare (Q : TriadicCube 2) :
    CompactSpace (closure (openCubeSet Q)) :=
  isCompact_iff_compactSpace.mp (isBounded_openCubeSet Q).isCompact_closure

/-- Restrict an actual parent scalar coefficient to the closed response
square, with its natural supremum norm bound. -/
noncomputable def physicalResponseRestriction {K : Set (Vec 2)}
    [CompactSpace K] (Q : TriadicCube 2)
    (hQ : closure (openCubeSet Q) ⊆ K) :
    C(K, ℝ) →L[ℝ] ResponseCoefficient (openCubeSet Q) :=
  (ContinuousMap.linearIsometryBoundedOfCompact
      (closure (openCubeSet Q)) ℝ ℝ).toLinearIsometry.toContinuousLinearMap.comp
    (ContinuousMap.compCLM ℝ ℝ
      ⟨fun x => ⟨x.1, hQ x.2⟩, by fun_prop⟩)

theorem physicalResponseRestriction_norm_le {K : Set (Vec 2)}
    [CompactSpace K] (Q : TriadicCube 2)
    (hQ : closure (openCubeSet Q) ⊆ K) (f : C(K, ℝ)) :
    ‖physicalResponseRestriction Q hQ f‖ ≤ ‖f‖ := by
  let e := ContinuousMap.linearIsometryBoundedOfCompact
    (closure (openCubeSet Q)) ℝ ℝ |>.toLinearIsometry
  change ‖e ((ContinuousMap.compCLM ℝ ℝ
    ⟨fun x => ⟨x.1, hQ x.2⟩, by fun_prop⟩) f)‖ ≤ ‖f‖
  rw [e.norm_map]
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
  intro x
  exact f.norm_coe_le_norm ⟨x.1, hQ x.2⟩

private theorem planarCoefficient_eq_of_symmPart' (ν : ℝ) (A : Mat 2)
    (hA : symmPart A = ν • (1 : Mat 2)) :
    responsePlanarCoefficient ν (A 1 0) = A := by
  have h00 := congrFun (congrFun hA 0) 0
  have h11 := congrFun (congrFun hA 1) 1
  have h01 := congrFun (congrFun hA 0) 1
  norm_num [symmPart, Matrix.smul_apply, Matrix.one_apply] at h00 h11 h01
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [responsePlanarCoefficient, responsePlanarJ] <;> linarith

private theorem symmPart_partialInsertedCoefficient'
    (M : ABKModel 2) (m : ℤ) (t : ℝ)
    (ω : Cutoff.CutoffSample 2) (x : Vec 2) :
    symmPart (Model.partialInsertedCoefficient M m t ω x) =
      M.nu • (1 : Mat 2) := by
  have hbase := Cutoff.symmPart_coefficientCutoff M.nu m ω x
  ext i j
  have hb := congrFun (congrFun hbase i) j
  have hj := (ω.1 (m + 1)).skew_entry x i j
  change (Cutoff.coefficientCutoff M.nu m ω x i j +
      Cutoff.coefficientCutoff M.nu m ω x j i) / 2 =
      (M.nu • (1 : Mat 2)) i j at hb
  change (Model.partialInsertedCoefficient M m t ω x i j +
      Model.partialInsertedCoefficient M m t ω x j i) / 2 = _
  change ((Cutoff.coefficientCutoff M.nu m ω x i j +
      Real.sqrt t * ω.1 (m + 1) x i j) +
      (Cutoff.coefficientCutoff M.nu m ω x j i +
      Real.sqrt t * ω.1 (m + 1) x j i)) / 2 = _
  rw [hj]
  linarith

theorem physical_response_coefficient_eq_actual
    {K : Set (Vec 2)} [CompactSpace K]
    (Q : TriadicCube 2) (hQ : closure (openCubeSet Q) ⊆ K)
    (M : ABKModel 2) (ell m : ℤ)
    (hK : K ⊆ openCubeSet (originCube 2 ell))
    (t : ℝ) (ω : Cutoff.CutoffSample 2)
    (x : Vec 2) (hx : x ∈ openCubeSet Q) :
    responsePlanarCoefficientField M.nu
        (physicalResponseRestriction Q hQ
          (modelInsertedScalar K m t ω)) x =
      Model.partialInsertedCoefficient M m t ω x := by
  have hxK : x ∈ K := hQ (subset_closure hx)
  have hkx : physicalResponseRestriction Q hQ
      (modelInsertedScalar K m t ω) ⟨x, subset_closure hx⟩ =
        modelInsertedScalar K m t ω ⟨x, hxK⟩ := by
    change modelInsertedScalar K m t ω
        ⟨x, hQ (subset_closure hx)⟩ = _
    rfl
  have hscalar := modelInsertedScalar_apply K M ell m hK t ω ⟨x, hxK⟩
  rw [responsePlanarCoefficientField, responseCoefficientExtension_eq _ hx,
    hkx, hscalar]
  exact planarCoefficient_eq_of_symmPart' M.nu _
    (symmPart_partialInsertedCoefficient' M m t ω x)

end ASDExplicitGamma.Scalar
