module

public import ASDExplicitGamma.Native.OldSignedPartitionCovarianceBound
public import ASDExplicitGamma.Triadic.VectorHaarSymmetry

/-! The literal output-rotated physical covariance field M in AN (2.6),
with its complete mode series and exact cellwise vector-Haar bill. -/
@[expose] public section
namespace ASDExplicitGamma.Native
open Homogenization MeasureTheory ASDExplicitGamma.Gaussian ASDExplicitGamma.Main ASDExplicitGamma.Triadic
open ASDExplicitGamma.Response
noncomputable section

/-- The actual two-load covariance M, with the source's output rotation J. -/
def oldSignedRemainderCovarianceField (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (plus : Bool) (i : Fin 2) (x : Vec 2) : Vec 2 :=
  planarQuarterTurn (fun k => oldSignedRemainderScalarCovariance Q b L plus (i,k) x)

/-- The complete source covariance series recovers the actual rotated M,
with no finite-rank stationarity assumption. -/
theorem old_signed_remainder_vector_covariance_hasSum (Q : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (plus : Bool) (i k : Fin 2) :
    ∀ᵐ x ∂normalizedCubeMeasure Q,HasSum (fun n : whiteBasisIndex =>
      q3Convolution b L h3Zero (whiteBasis n) x *
        matVecMul responsePlanarJ (fun l => oldSignedRemainderCoordinate Q b L plus n (i,l) x) k)
      (oldSignedRemainderCovarianceField Q b L plus i x k) := by
  filter_upwards [old_signed_remainder_scalar_covariance_hasSum Q b L plus (i,0),
    old_signed_remainder_scalar_covariance_hasSum Q b L plus (i,1)] with x h0 h1
  have hJ (v : Vec 2) : matVecMul responsePlanarJ v=planarQuarterTurn v := by
    funext l
    fin_cases l <;> simp [matVecMul,responsePlanarJ,Fin.sum_univ_two,planarQuarterTurn]
  simp_rw [hJ]
  fin_cases k
  · change HasSum (fun n => q3Convolution b L h3Zero (whiteBasis n) x *
      (-oldSignedRemainderCoordinate Q b L plus n (i,1) x))
      (-oldSignedRemainderScalarCovariance Q b L plus (i,1) x)
    apply h1.neg.congr_fun
    intro n
    ring
  · change HasSum (fun n => q3Convolution b L h3Zero (whiteBasis n) x *
      oldSignedRemainderCoordinate Q b L plus n (i,0) x)
      (oldSignedRemainderScalarCovariance Q b L plus (i,0) x)
    exact h0

/-- The vector-Haar beta bill agrees exactly with the four scalar
covariance coordinates already controlled by the Hilbert product proof. -/
theorem old_signed_covariance_vector_haar_energy (Q U : TriadicCube 2) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (plus : Bool) :
    (∑ i : Fin 2,vectorPositiveHaarNorm U (oldSignedRemainderCovarianceField Q b L plus i)^2)=
      ∑ a,hilbertPositiveHaarNorm U (Real.sqrt 3) (oldSignedRemainderScalarCovariance Q b L plus a)^2 := by
  have he i : vectorPositiveHaarNorm U (oldSignedRemainderCovarianceField Q b L plus i)=
      vectorPositiveHaarNorm U (fun x k => oldSignedRemainderScalarCovariance Q b L plus (i,k) x) :=
    vectorPositiveHaarNorm_quarterTurn U _
  simp_rw [he]
  simp only [vectorPositiveHaarNorm,vectorPositiveHaarEnergy,hilbertPositiveHaarNorm,
    hilbertPrimalEnergy_real]
  simp_rw [Real.sq_sqrt (primalEnergy_nonneg U (Real.sqrt 3) (Real.sqrt_nonneg _) _),
    Real.sq_sqrt (Finset.sum_nonneg (fun k _ => primalEnergy_nonneg U (Real.sqrt 3) (Real.sqrt_nonneg _) _))]
  rw [Fintype.sum_prod_type]

/-- AN (2.6) for the actual source vector fields Mplus and Mminus, with
all cell and load sums and the unchanged output J. -/
theorem old_signed_covariance_beta_bound (Q : TriadicCube 2) (depth : ℕ) (b : ℝ)
    (L : {l : ℝ // 0 < l}) (plus : Bool) :
    Real.sqrt (descendantsAverage Q depth (fun U => ∑ i : Fin 2,
      vectorPositiveHaarNorm U (oldSignedRemainderCovarianceField Q b L plus i)^2))≤
      |b| *Real.sqrt (oldSignedFlatBoundaryEnergy Q b L/2)+
        (cubeScaleFactor Q/(3:ℝ)^depth)*planarC1*
          (Real.sqrt (mainFlatSigmaSq b L)*Real.sqrt (oldSignedFlatBoundaryEnergy Q b L/2)+
            2*|b| *Real.sqrt (mainFlatSigmaSq b L)) := by
  simp_rw [old_signed_covariance_vector_haar_energy]
  exact old_signed_partition_covariance_bound Q depth b L plus

end
end ASDExplicitGamma.Native
