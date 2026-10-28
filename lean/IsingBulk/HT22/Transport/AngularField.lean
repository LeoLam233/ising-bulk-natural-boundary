import IsingBulk.HT22.Transport.MixedCovariance
import IsingBulk.Preferred22.Transport

/-! F001 angular representative for the new mixed-covariance residual.
The matrix algebra is reused generically; the LT divided-pair residual is not. -/
namespace IsingBulk.HT22
noncomputable section
open scoped BigOperators
open IsingBulk.Preferred22

def mixedAngularField {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ)
    (u v uDot : Fin N → ℂ) : Fin N → ℂ :=
  preferredAngularRepresentative M uDot v (mixedCollectiveField u v uDot)

theorem mixedAngularField_tangent {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ)
    (u v uDot : Fin N → ℂ)
    (hcol : ∀ j, (∑ i, M i j)=1) (hM : M.det≠0)
    (hR : mixedCovariance u v≠0) :
    (∑ i, mixedAngularField M u v uDot i)=0 :=
  preferredAngularRepresentative_tangent M uDot v (mixedCollectiveField u v uDot)
    hcol hM (mixedCollectiveField_weighted u v uDot hR)

/-- The residual equation is a literal matrix equality with all coupled
occupancy terms retained in M. -/
theorem mixedAngularField_equation {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ)
    (u v uDot : Fin N → ℂ) (hM : M.det≠0) :
    M.mulVec (mixedAngularField M u v uDot) =
      -(fun i => uDot i+v i*mixedCollectiveField u v uDot i) := by
  unfold mixedAngularField preferredAngularRepresentative
  change M.mulVec (-(M⁻¹.mulVec (fun i => uDot i+v i*mixedCollectiveField u v uDot i))) = _
  rw [Matrix.mulVec_neg,Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hM),Matrix.one_mulVec]

/-- Exact fixed-v phase-freezing algebra, before applying the actual source
chain rules. No moving-coordinate correction is present in F001. -/
theorem mixedAngularField_phase_algebra {N : ℕ}
    (M : Matrix (Fin N) (Fin N) ℂ) (u v uDot : Fin N → ℂ)
    (hM : M.det≠0) (hv : ∀ i, v i≠0) (hR : mixedCovariance u v≠0) :
    (∑ i, -uDot i/v i)-
      (∑ j, mixedAngularField M u v uDot j * (∑ i, ((v i)⁻¹-1)*M i j))=0 := by
  let B := mixedCollectiveField u v uDot
  let V := mixedAngularField M u v uDot
  have hm (i : Fin N) : (∑ j, M i j*V j)=-(uDot i+v i*B i) :=
    congrFun (mixedAngularField_equation M u v uDot hM) i
  have hs : (∑ j, V j*(∑ i, ((v i)⁻¹-1)*M i j))=
      ∑ i, ((v i)⁻¹-1)*(-(uDot i+v i*B i)) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = ((v i)⁻¹-1)*(∑ j, M i j*V j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [hm]
  change (∑ i, -uDot i/v i)-(∑ j, V j*(∑ i, ((v i)⁻¹-1)*M i j))=0
  rw [hs,← Finset.sum_sub_distrib]
  calc
    _ = ∑ i, (B i-v i*B i-uDot i) := by
      apply Finset.sum_congr rfl
      intro i _
      field_simp [hv i]
      ring
    _ = 0 := by
      simp only [Finset.sum_sub_distrib]
      dsimp only [B]
      rw [mixedCollectiveField_sum,mixedCollectiveField_weighted u v uDot hR]
      ring

end
end IsingBulk.HT22
