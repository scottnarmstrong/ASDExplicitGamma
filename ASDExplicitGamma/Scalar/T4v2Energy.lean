module

public import ASDExplicitGamma.Scalar.T4v2Comp
public import ASDExplicitGamma.Scalar.T4v2Weak
public import ASDExplicitGamma.Scalar.PairInnerMain

/-! T4 v2: the weak energy of the corrected forced part of one mode, in terms of the actual OLD
maximizer. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian MeasureTheory
open scoped InnerProductSpace

attribute [local irreducible] Homogenization.descendantsAtDepth

noncomputable section

namespace Cfg''

variable (C : Cfg'')

theorem t4v2_pot_plain (X : C.Xs) :
    (rep'' C.nQ (potMap C.Q (X : HilbertVectorL2 (openCubeSet C.Q)))).toH1Function.grad =ᵐ[
      volumeMeasureOn (openCubeSet C.Q)] hilbertVectorL2ToVectorL2 (X : HilbertVectorL2 (openCubeSet C.Q)) := by
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet C.Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet C.Q).isFiniteMeasure_restrict_volume
  apply ae_of_toHilbert_eq (H1Function.grad_memVectorL2 _) (Lp.memLp _)
  change (rep'' C.nQ (potMap C.Q (X : HilbertVectorL2 (openCubeSet C.Q)))).toH1Function.gradToHilbertVectorL2 =
    toHilbertVectorL2OfVecField (Lp.memLp (hilbertVectorL2ToVectorL2 (X : HilbertVectorL2 (openCubeSet C.Q))))
  rw [fw_toHilbertVectorL2OfVecField_hilbertVectorL2ToVectorL2, rep_class]
  exact potMap_gradient C.Q X

theorem t4v2_load_plain (u : H10Function (openCubeSet C.Q)) :
    hilbertVectorL2ToVectorL2 (fwLoad C.Q u : HilbertVectorL2 (openCubeSet C.Q)) =ᵐ[
      volumeMeasureOn (openCubeSet C.Q)] u.toH1Function.grad := by
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet C.Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet C.Q).isFiniteMeasure_restrict_volume
  apply ae_of_toHilbert_eq (Lp.memLp _) (H1Function.grad_memVectorL2 _)
  change toHilbertVectorL2OfVecField (Lp.memLp (hilbertVectorL2ToVectorL2
      (u.toH1Function.gradToHilbertVectorL2))) = u.toH1Function.gradToHilbertVectorL2
  exact fw_toHilbertVectorL2OfVecField_hilbertVectorL2ToVectorL2 _

theorem t4v2_mode_energy (hQ : openCubeSet C.Q ⊆ openRectangle C.a C.b C.c C.d)
    (old : C(closedRectangle C.a C.b C.c C.d, ℝ)) (j : ℕ)
    (k : ResponseCoefficient (openCubeSet C.Q)) (hk : C.Rest old = k)
    (u : H10Function (openCubeSet C.Q)) (hF : C.Fl (C.Hs j) = -(fwLoad C.Q u))
    (Z : Vec 2 → BlockVec 2)
    (hZ : IsScalarOldMaximizer C.Q C.ν C.σ k (fun x => u.toH1Function.grad x) Z) :
    lemmaVTiledWeakEnergy C.Q 134
        (rep'' C.nQ (potMap C.Q ((C.forcedR old j).ofLp.2 : HilbertVectorL2
          (openCubeSet C.Q)))).toH1Function.grad +
      lemmaVTiledWeakEnergy C.Q 134 (rep2 C.nQ 134 (C.forcedR old j).ofLp.1).1 =
    ((C.σ ^ 2)⁻¹) * (lemmaVTiledWeakEnergy C.Q 134
        (fun x j => (Z x).1 j - u.toH1Function.grad x j) +
      lemmaVTiledWeakEnergy C.Q 134
        (fun x => (scalarCoefficientFlux (responseFramePlanarCoefficientField C.ν C.σ k) Z x).2)) := by
  letI : IsFiniteMeasure (volumeMeasureOn (openCubeSet C.Q)) :=
    (isOpenBoundedConvexDomain_openCubeSet C.Q).isFiniteMeasure_restrict_volume
  have hc := C.forcedR_comp hQ old j k hk u hF
  have hpair := fw_pair_ident C.Q C.ν C.σ C.hν C.hσ k u Z hZ
  have hx : (C.forcedR old j).ofLp.2 = (-C.σ⁻¹) • ((fwPairSolution C.Q C.ν C.σ C.hν C.hσ k u).ofLp.2 -
      fwLoad C.Q u) := by
    rw [hc]; simp [inr_apply']
  have hy : (C.forcedR old j).ofLp.1 = (-C.σ⁻¹) • (fwPairSolution C.Q C.ν C.σ C.hν C.hσ k u).ofLp.1 := by
    rw [hc]; simp [inr_apply']
  -- potential slot
  have hpot : (rep'' C.nQ (potMap C.Q ((C.forcedR old j).ofLp.2 : HilbertVectorL2
          (openCubeSet C.Q)))).toH1Function.grad =ᵐ[volumeMeasureOn (openCubeSet C.Q)]
      fun x => (-C.σ⁻¹) • (fun x j => (Z x).1 j - u.toH1Function.grad x j) x := by
    refine (C.t4v2_pot_plain _).trans ?_
    rw [hx]
    have h1 := Lp.coeFn_smul (-C.σ⁻¹) (hilbertVectorL2ToVectorL2
      ((fwPairSolution C.Q C.ν C.σ C.hν C.hσ k u).ofLp.2 : HilbertVectorL2 (openCubeSet C.Q)) -
        hilbertVectorL2ToVectorL2 (fwLoad C.Q u : HilbertVectorL2 (openCubeSet C.Q)))
    have h2 := Lp.coeFn_sub (hilbertVectorL2ToVectorL2
      ((fwPairSolution C.Q C.ν C.σ C.hν C.hσ k u).ofLp.2 : HilbertVectorL2 (openCubeSet C.Q)))
      (hilbertVectorL2ToVectorL2 (fwLoad C.Q u : HilbertVectorL2 (openCubeSet C.Q)))
    have e : (((-C.σ⁻¹) • ((fwPairSolution C.Q C.ν C.σ C.hν C.hσ k u).ofLp.2 -
        fwLoad C.Q u) : C.Xs) : HilbertVectorL2 (openCubeSet C.Q)) =
        (-C.σ⁻¹) • (((fwPairSolution C.Q C.ν C.σ C.hν C.hσ k u).ofLp.2 :
          HilbertVectorL2 (openCubeSet C.Q)) - (fwLoad C.Q u : HilbertVectorL2 (openCubeSet C.Q))) := by
      simp
    rw [e, map_smul, map_sub]
    filter_upwards [h1, h2, hpair.1, C.t4v2_load_plain u] with x a b c d
    rw [a, Pi.smul_apply, b, Pi.sub_apply, c, d]
    ext j
    simp
  have hflux : (rep2 C.nQ 134 (C.forcedR old j).ofLp.1).1 =ᵐ[volumeMeasureOn (openCubeSet C.Q)]
      fun x => (-C.σ⁻¹) • (fun x => (scalarCoefficientFlux
        (responseFramePlanarCoefficientField C.ν C.σ k) Z x).2) x := by
    change (fun z => (hilbertVectorL2ToVectorL2 (C.forcedR old j).ofLp.1 : Vec 2 → Vec 2) z) =ᵐ[_] _
    rw [hy, map_smul]
    have h1 := Lp.coeFn_smul (-C.σ⁻¹) (hilbertVectorL2ToVectorL2
      (fwPairSolution C.Q C.ν C.σ C.hν C.hσ k u).ofLp.1)
    filter_upwards [h1, hpair.2] with x a b
    rw [a, Pi.smul_apply, b]
  rw [t4v2_tiled_scale C.Q (-C.σ⁻¹) hpot, t4v2_tiled_scale C.Q (-C.σ⁻¹) hflux]
  have hsq : (-C.σ⁻¹) ^ 2 = (C.σ ^ 2)⁻¹ := by rw [neg_sq, inv_pow]
  rw [hsq]
  ring

end Cfg''

end

end ASDExplicitGamma.Scalar
