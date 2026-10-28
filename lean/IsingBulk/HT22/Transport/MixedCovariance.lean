import Mathlib.Tactic
import Mathlib.Basic.Complex.BigOperators

/-! F001 (7.12)-(7.13): literal bilinear complex covariance, not a
Hermitian covariance or the LT22 squared-angle denominator. No slope
quotients are used, hence no artificial partial-diagonal denominators. -/
namespace IsingBulk.HT22
noncomputable section
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

def mixedCovariance (u v : ι → ℂ) : ℂ :=
  (∑ i, ∑ l, (u i-u l)*(v i-v l))/2

def centeredAngleSum (u : ι → ℂ) (i : ι) : ℂ := ∑ l, (u i-u l)

def mixedCollectiveField (u v uDot : ι → ℂ) (i : ι) : ℂ :=
  (-(∑ l, uDot l))/mixedCovariance u v * centeredAngleSum u i

theorem centeredAngleSum_total (u : ι → ℂ) :
    (∑ i, centeredAngleSum u i)=0 := by
  unfold centeredAngleSum
  simp only [Finset.sum_sub_distrib]
  simp [← Finset.mul_sum]

theorem centeredAngleSum_weighted (u v : ι → ℂ) :
    (∑ i, v i*centeredAngleSum u i)=mixedCovariance u v := by
  have hp (i l : ι) :
      v i*(u i-u l)+v l*(u l-u i)=(u i-u l)*(v i-v l) := by ring
  have hh : (∑ i, ∑ l, (v i*(u i-u l)+v l*(u l-u i))) =
      ∑ i, ∑ l, (u i-u l)*(v i-v l) := by
    apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_congr rfl (fun l _ => hp i l)
  simp only [Finset.sum_add_distrib] at hh
  have hs : (∑ i, ∑ l, v l*(u l-u i))=(∑ i, ∑ l, v i*(u i-u l)) :=
    Finset.sum_comm
  rw [hs] at hh
  unfold mixedCovariance centeredAngleSum
  simp only [Finset.mul_sum]
  linear_combination hh/2

theorem mixedCovariance_eq_upper [LinearOrder ι] (u v : ι → ℂ) :
    mixedCovariance u v =
      ∑ i, ∑ l, if i<l then (u i-u l)*(v i-v l) else 0 := by
  let H := fun i l => if i<l then (u i-u l)*(v i-v l) else 0
  have hp (i l : ι) : (u i-u l)*(v i-v l)=H i l+H l i := by
    dsimp [H]
    rcases lt_trichotomy i l with h | h | h
    · simp [h,not_lt.mpr h.le]
    · subst l; simp
    · simp [h,not_lt.mpr h.le]; ring
  have hh : (∑ i, ∑ l, (u i-u l)*(v i-v l))=
      (∑ i, ∑ l, H i l)+(∑ i, ∑ l, H i l) := by
    simp_rw [hp,Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun i l => H l i)]
  unfold mixedCovariance
  rw [hh]
  dsimp [H]
  ring

theorem mixedCollectiveField_sum (u v uDot : ι → ℂ) :
    (∑ i, mixedCollectiveField u v uDot i)=0 := by
  simp only [mixedCollectiveField,← Finset.mul_sum,centeredAngleSum_total,mul_zero]

theorem mixedCollectiveField_weighted (u v uDot : ι → ℂ)
    (hR : mixedCovariance u v ≠ 0) :
    (∑ i, v i*mixedCollectiveField u v uDot i)=-(∑ i, uDot i) := by
  calc
    _ = (-(∑ l, uDot l))/mixedCovariance u v *
        (∑ i, v i*centeredAngleSum u i) := by
      simp only [mixedCollectiveField,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by rw [centeredAngleSum_weighted]; field_simp

/-- Any fixed complex projection with positive real value certifies the
actual bilinear denominator is nonzero; no claim Re R > 0 is made. -/
theorem mixedCovariance_ne_zero_of_projection (u v : ι → ℂ) (phase : ℂ)
    (h : 0 < (phase*mixedCovariance u v).re) : mixedCovariance u v ≠ 0 := by
  intro hz
  simp [hz] at h

/-- The pairwise projected sector estimate sums without replacing the
bilinear covariance by a Hermitian expression. The analytic pair estimate
is intentionally explicit and must be supplied from the actual contour. -/
theorem mixedCovariance_projected_lower (u v : ι → ℂ) (θ : ι → ℝ)
    (phase : ℂ) (c : ℝ)
    (hpair : ∀ i l, c*(θ i-θ l)^2 ≤ (phase*((u i-u l)*(v i-v l))).re) :
    c*((∑ i, ∑ l, (θ i-θ l)^2)/2) ≤ (phase*mixedCovariance u v).re := by
  have hs : (∑ i, ∑ l, c*(θ i-θ l)^2) ≤
      ∑ i, ∑ l, (phase*((u i-u l)*(v i-v l))).re := by
    apply Finset.sum_le_sum
    intro i _
    exact Finset.sum_le_sum (fun l _ => hpair i l)
  have he : (phase*mixedCovariance u v).re =
      (∑ i, ∑ l, (phase*((u i-u l)*(v i-v l))).re)/2 := by
    simp only [mixedCovariance,← mul_div_assoc,Finset.mul_sum,Complex.div_ofNat_re,
      Complex.re_sum]
  rw [he]
  simp only [← Finset.mul_sum] at hs
  linarith

end
end IsingBulk.HT22
