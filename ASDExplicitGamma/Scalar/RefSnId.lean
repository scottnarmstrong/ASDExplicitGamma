module

public import ASDExplicitGamma.Scalar.RefDefect

/-! Successor of the Wick source identification. -/
@[expose] public section
namespace ASDExplicitGamma.Scalar

open Homogenization MeasureTheory ASDExplicitGamma.Response ASDExplicitGamma.Triadic
  ASDExplicitGamma.Variational ASDExplicitGamma.Gaussian ASDExplicitGamma.Main
open Algsuperdiff.Section3 ASDExplicitGamma.Native ASDExplicitGamma.Inverse Filter
open scoped InnerProductSpace BigOperators ENNReal Topology

noncomputable section

namespace Cfg''

variable (C : Cfg'')

/-- The flux-slot Wick family (negative symmetrized Lemma V rows). -/
def BFoR (old : C(closedRectangle C.a C.b C.c C.d, ℝ)) (n : ℕ) :
    Fin n → Fin n → TiledHaarField C.Q 134 := fun i j =>
  -(symRows C.nQ 134 C.amp C.L (fun i : Fin n => eOpt i)
    (fun j : Fin n => rep'' C.nQ (C.zpotR old j)) i j)

/-- The potential-slot Wick family. -/
def BGoR (old : C(closedRectangle C.a C.b C.c C.d, ℝ)) (n : ℕ) :
    Fin n → Fin n → TiledHaarField C.Q 134 :=
  gSymRows C.nQ 134 C.amp C.L (fun i : Fin n => eOpt i)
    (fun j : Fin n => rep2 C.nQ 134 (C.dyR old j))

theorem BFoR_apply (old : C(closedRectangle C.a C.b C.c C.d, ℝ)) (n : ℕ) (x : Fin n → ℝ)
    (p : Vec 2) :
    (psdDefectSource (C.BFoR old n) x).1 p = ∑ ij : Fin n × Fin n, (x ij.1 * x ij.2) •
      (-((rowEltOpt C.Q 134 C.amp C.L (eOpt ij.1)
        (rep'' C.nQ (C.zpotR old ij.2))).1 p)) := by
  have h1 : psdDefectSource (C.BFoR old n) x = -psdDefectSource (symRows C.nQ 134 C.amp C.L
      (fun i : Fin n => eOpt i) (fun j : Fin n => rep'' C.nQ (C.zpotR old j))) x :=
    psdDefectSource_neg _ x
  rw [h1, psdDefectSource_symRows]
  have := psdDefectSource_coe_apply (fun i j : Fin n => rowEltOpt C.Q 134 C.amp C.L (eOpt i)
    (rep'' C.nQ (C.zpotR old j))) x p
  have hneg : ∀ a : TiledHaarField C.Q 134, (-a).1 p = -(a.1 p) := fun a => rfl
  rw [hneg, this, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun ij _ => ?_
  rw [smul_neg]

theorem BGoR_apply (old : C(closedRectangle C.a C.b C.c C.d, ℝ)) (n : ℕ) (x : Fin n → ℝ)
    (p : Vec 2) :
    (psdDefectSource (C.BGoR old n) x).1 p = ∑ ij : Fin n × Fin n, (x ij.1 * x ij.2) •
      ((gSlotOpt C.nQ 134 C.amp C.L (eOpt ij.1)
        (rep2 C.nQ 134 (C.dyR old ij.2))).1 p) := by
  have h1 : psdDefectSource (C.BGoR old n) x = psdDefectSource
      (fun i j : Fin n => gSlotOpt C.nQ 134 C.amp C.L (eOpt i)
        (rep2 C.nQ 134 (C.dyR old j))) x :=
    psdDefectSource_gsymRows C.nQ 134 C.amp C.L (fun i : Fin n => eOpt i)
      (fun j : Fin n => rep2 C.nQ 134 (C.dyR old j)) x
  rw [h1]
  exact psdDefectSource_coe_apply (fun i j : Fin n => gSlotOpt C.nQ 134 C.amp C.L (eOpt i)
    (rep2 C.nQ 134 (C.dyR old j))) x p

theorem sbil_termR (old : C(closedRectangle C.a C.b C.c C.d, ℝ)) (i j : ℕ) :
    sbil C.Vm C.FlR (C.Bop old) (C.U old) C.σ (C.Hs i) (C.Hs j) =
      (WithLp.toLp 2 (C.Vm (C.Hs i) (C.dxR old j),
        -(ContinuousLinearMap.adjoint (C.Vm (C.Hs i))) (C.dyR old j)) : C.Pr) := by
  rw [sbil_apply]
  refine WithLp.ofLp_injective 2 ?_
  rw [pureFluxBlockOperator_apply]
  ext <;> simp [dxR, dyR, deltaR]

theorem flux_sumR (old : C(closedRectangle C.a C.b C.c C.d, ℝ)) (n : ℕ) (x : Fin n → ℝ)
    (hF : MemVectorL2 (openCubeSet C.Q) (psdDefectSource (C.BFoR old n) x).1) :
    ∑ ij : Fin n × Fin n, (x ij.1 * x ij.2) • C.Vm (C.Hs ij.1) (C.dxR old ij.2) =
      fluxSource C.Q hF := by
  have hf : ∀ ij : Fin n × Fin n, MemVectorL2 (openCubeSet C.Q)
      (fun p => -((rowEltOpt C.Q 134 C.amp C.L (eOpt ij.1)
        (rep'' C.nQ (C.zpotR old ij.2))).1 p)) :=
    fun ij => (rowEltOpt_memL2 C.nQ 134 C.amp C.L _ _).neg
  have h := memVectorL2_finsum (U := openCubeSet C.Q) (Finset.univ : Finset (Fin n × Fin n))
    (fun ij => x ij.1 * x ij.2) (fun ij p => -((rowEltOpt C.Q 134 C.amp C.L (eOpt ij.1)
        (rep'' C.nQ (C.zpotR old ij.2))).1 p)) hf
  have e : (psdDefectSource (C.BFoR old n) x).1 = fun p => ∑ ij : Fin n × Fin n,
      (x ij.1 * x ij.2) • (-((rowEltOpt C.Q 134 C.amp C.L (eOpt ij.1)
        (rep'' C.nQ (C.zpotR old ij.2))).1 p)) := funext (BFoR_apply C old n x)
  have hA : fluxSource C.Q hF = fluxSource C.Q h := fluxSource_congr C.Q e hF h
  have hB := fluxSource_finsum C.Q Finset.univ (fun ij : Fin n × Fin n => x ij.1 * x ij.2)
      (fun ij p => -((rowEltOpt C.Q 134 C.amp C.L (eOpt ij.1)
        (rep'' C.nQ (C.zpotR old ij.2))).1 p)) hf h
  calc ∑ ij : Fin n × Fin n, (x ij.1 * x ij.2) • C.Vm (C.Hs ij.1) (C.dxR old ij.2)
      = ∑ ij : Fin n × Fin n, (x ij.1 * x ij.2) • fluxSource C.Q (hf ij) :=
        Finset.sum_congr rfl (fun ij _ => by
          rw [fslot_term_genR C old ij.1 ij.2 (eOpt ij.1) rfl (hf ij)])
    _ = fluxSource C.Q h := hB.symm
    _ = fluxSource C.Q hF := hA.symm

theorem pot_sumR (old : C(closedRectangle C.a C.b C.c C.d, ℝ)) (n : ℕ) (x : Fin n → ℝ)
    (hG : MemVectorL2 (openCubeSet C.Q) (psdDefectSource (C.BGoR old n) x).1) :
    ∑ ij : Fin n × Fin n, (x ij.1 * x ij.2) •
      (-(ContinuousLinearMap.adjoint (C.Vm (C.Hs ij.1))) (C.dyR old ij.2)) =
      potSource C.Q hG := by
  have hf : ∀ ij : Fin n × Fin n, MemVectorL2 (openCubeSet C.Q)
      (gSlotOpt C.nQ 134 C.amp C.L (eOpt ij.1) (rep2 C.nQ 134 (C.dyR old ij.2))).1 :=
    fun ij => gslotOpt_memL2 C.nQ 134 C.amp C.L _ _
  have h := memVectorL2_finsum (U := openCubeSet C.Q) (Finset.univ : Finset (Fin n × Fin n))
    (fun ij => x ij.1 * x ij.2) (fun ij => (gSlotOpt C.nQ 134 C.amp C.L (eOpt ij.1)
      (rep2 C.nQ 134 (C.dyR old ij.2))).1) hf
  have e : (psdDefectSource (C.BGoR old n) x).1 = fun p => ∑ ij : Fin n × Fin n,
      (x ij.1 * x ij.2) • ((gSlotOpt C.nQ 134 C.amp C.L (eOpt ij.1)
        (rep2 C.nQ 134 (C.dyR old ij.2))).1 p) := funext (BGoR_apply C old n x)
  have hA : potSource C.Q hG = potSource C.Q h := potSource_congr C.Q e hG h
  have hB := potSource_finsum C.Q Finset.univ (fun ij : Fin n × Fin n => x ij.1 * x ij.2)
      (fun ij => (gSlotOpt C.nQ 134 C.amp C.L (eOpt ij.1)
        (rep2 C.nQ 134 (C.dyR old ij.2))).1) hf h
  calc ∑ ij : Fin n × Fin n, (x ij.1 * x ij.2) •
        (-(ContinuousLinearMap.adjoint (C.Vm (C.Hs ij.1))) (C.dyR old ij.2))
      = ∑ ij : Fin n × Fin n, (x ij.1 * x ij.2) • potSource C.Q (hf ij) :=
        Finset.sum_congr rfl (fun ij _ => by
          rw [gslot_term_genR C old ij.1 ij.2 (eOpt ij.1) rfl (hf ij)])
    _ = potSource C.Q h := hB.symm
    _ = potSource C.Q hG := hA.symm

theorem BFoR_memL2 (old : C(closedRectangle C.a C.b C.c C.d, ℝ)) (n : ℕ) (x : Fin n → ℝ) :
    MemVectorL2 (openCubeSet C.Q) (psdDefectSource (C.BFoR old n) x).1 := by
  have hf : ∀ ij : Fin n × Fin n, MemVectorL2 (openCubeSet C.Q)
      (fun p => -((rowEltOpt C.Q 134 C.amp C.L (eOpt ij.1)
        (rep'' C.nQ (C.zpotR old ij.2))).1 p)) :=
    fun ij => (rowEltOpt_memL2 C.nQ 134 C.amp C.L _ _).neg
  have h := memVectorL2_finsum (U := openCubeSet C.Q) (Finset.univ : Finset (Fin n × Fin n))
    (fun ij => x ij.1 * x ij.2) (fun ij p => -((rowEltOpt C.Q 134 C.amp C.L (eOpt ij.1)
        (rep'' C.nQ (C.zpotR old ij.2))).1 p)) hf
  have e : (psdDefectSource (C.BFoR old n) x).1 = fun p => ∑ ij : Fin n × Fin n,
      (x ij.1 * x ij.2) • (-((rowEltOpt C.Q 134 C.amp C.L (eOpt ij.1)
        (rep'' C.nQ (C.zpotR old ij.2))).1 p)) := funext (BFoR_apply C old n x)
  rw [e]; exact h

theorem BGoR_memL2 (old : C(closedRectangle C.a C.b C.c C.d, ℝ)) (n : ℕ) (x : Fin n → ℝ) :
    MemVectorL2 (openCubeSet C.Q) (psdDefectSource (C.BGoR old n) x).1 := by
  have hf : ∀ ij : Fin n × Fin n, MemVectorL2 (openCubeSet C.Q)
      (gSlotOpt C.nQ 134 C.amp C.L (eOpt ij.1) (rep2 C.nQ 134 (C.dyR old ij.2))).1 :=
    fun ij => gslotOpt_memL2 C.nQ 134 C.amp C.L _ _
  have h := memVectorL2_finsum (U := openCubeSet C.Q) (Finset.univ : Finset (Fin n × Fin n))
    (fun ij => x ij.1 * x ij.2) (fun ij => (gSlotOpt C.nQ 134 C.amp C.L (eOpt ij.1)
      (rep2 C.nQ 134 (C.dyR old ij.2))).1) hf
  have e : (psdDefectSource (C.BGoR old n) x).1 = fun p => ∑ ij : Fin n × Fin n,
      (x ij.1 * x ij.2) • ((gSlotOpt C.nQ 134 C.amp C.L (eOpt ij.1)
        (rep2 C.nQ 134 (C.dyR old ij.2))).1 p) := funext (BGoR_apply C old n x)
  rw [e]; exact h

/-- **The Wick partial sum is the two-slot source.** -/
theorem sn_identR (old : C(closedRectangle C.a C.b C.c C.d, ℝ)) (n : ℕ) (x : Fin n → ℝ) :
    sbil C.Vm C.FlR (C.Bop old) (C.U old) C.σ (∑ i : Fin n, x i • C.Hs i)
        (∑ i : Fin n, x i • C.Hs i) =
      (WithLp.toLp 2 (fluxSource C.Q (C.BFoR_memL2 old n x),
        potSource C.Q (C.BGoR_memL2 old n x)) : C.Pr) := by
  rw [sbil_expand]
  have hterm : ∀ i j : Fin n, (x i * x j) • sbil C.Vm C.FlR (C.Bop old) (C.U old) C.σ
      (C.Hs i) (C.Hs j) = (WithLp.toLp 2 ((x i * x j) • C.Vm (C.Hs i) (C.dxR old j),
        (x i * x j) • (-(ContinuousLinearMap.adjoint (C.Vm (C.Hs i))) (C.dyR old j))) : C.Pr) := by
    intro i j
    rw [sbil_termR]
    refine WithLp.ofLp_injective 2 ?_
    ext <;> simp
  simp only [hterm]
  rw [toLp_sum_prod (fun i j => (x i * x j) • C.Vm (C.Hs i) (C.dxR old j))
    (fun i j => (x i * x j) • (-(ContinuousLinearMap.adjoint (C.Vm (C.Hs i))) (C.dyR old j)))]
  have h1 := flux_sumR C old n x (C.BFoR_memL2 old n x)
  have h2 := pot_sumR C old n x (C.BGoR_memL2 old n x)
  rw [h1, h2]


end Cfg''

end

end ASDExplicitGamma.Scalar
