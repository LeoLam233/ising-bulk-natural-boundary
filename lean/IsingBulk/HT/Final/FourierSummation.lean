import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecificLimits.Normed
import IsingBulk.HT.Final.LatticeSummation

/-! Two summation mechanisms used in the physical full-site identification.
The vertical geometric kernel is evaluated exactly. The horizontal Fourier
constraint follows from Mathlib's genuine Fourier inversion theorem, under
its required absolute-summability premise. Identifying the actual Ising
coefficients with those Fourier coefficients remains separate. -/
namespace IsingBulk.HT.Final
noncomputable section
open scoped BigOperators

/-- The two-sided vertical displacement series is genuinely summable before
its geometric closed form is used. -/
theorem vertical_displacement_geometric_summable {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun m : ℤ => z^m.natAbs) := by
  have hs := summable_geometric_of_norm_lt_one hz
  apply Summable.of_nat_of_neg
  · simpa using hs
  · simpa using hs

/-- Exact full vertical lattice kernel, not a one-sided geometric surrogate. -/
theorem vertical_displacement_geometric_sum {z : ℂ} (hz : ‖z‖ < 1) :
    (∑' m : ℤ, z^m.natAbs) = (1+z)/(1-z) := by
  have hs := summable_geometric_of_norm_lt_one hz
  have hnat : Summable (fun m : ℕ => z^((m:ℤ).natAbs)) := by simpa using hs
  have hneg : Summable (fun m : ℕ => z^((-(m:ℤ)).natAbs)) := by simpa using hs
  have heq : (∑' m : ℤ, z^m.natAbs) =
      (∑' m : ℕ, z^m)+(∑' m : ℕ, z^m)-1 := by
    simpa using Summable.tsum_of_nat_of_neg
      (f := fun m : ℤ => z^m.natAbs) hnat hneg
  rw [heq, tsum_geometric_of_norm_lt_one hz]
  have hgap : (1:ℂ)-z ≠ 0 := by
    intro he
    have hz1 : z=1 := (sub_eq_zero.mp he).symm
    rw [hz1, norm_one] at hz
    exact (lt_irrefl (1:ℝ)) hz
  field_simp [hgap]
  ring

/-- Evaluation of the Fourier sum at zero implements the horizontal
zero-total-angle constraint. The coefficient premise is an equality, not an
abstract continuation or asymptotic input. -/
theorem horizontal_fourier_sum_at_zero {T : ℝ} [Fact (0 < T)]
    (f : C(AddCircle T, ℂ)) {q : ℤ → ℂ}
    (hq : Summable q) (hcoeff : ∀ n : ℤ, q n=fourierCoeff f n) :
    (∑' n : ℤ, q n) = f 0 := by
  have hf : Summable (fourierCoeff f) := hq.congr hcoeff
  calc
    (∑' n : ℤ, q n) = ∑' n : ℤ, fourierCoeff f n := tsum_congr hcoeff
    _ = f 0 := by
      simpa only [fourier_eval_zero, smul_eq_mul, mul_one] using
        (has_pointwise_sum_fourier_series_of_summable hf (0 : AddCircle T)).tsum_eq

/-- Real-periodic form of the same theorem. This packages the actual
continuous periodic fiber integral on `AddCircle` without requiring the
physical proof to construct a quotient map by hand. -/
theorem horizontal_real_fourier_sum_at_zero {T : ℝ} [hT : Fact (0 < T)]
    (H : ℝ → ℂ) (hc : Continuous H) (hp : Function.Periodic H T)
    {q : ℤ → ℂ} (hq : Summable q)
    (hcoeff : ∀ n : ℤ, q n = fourierCoeffOn hT.out H n) :
    (∑' n : ℤ, q n) = H 0 := by
  have he : H 0=H T := by
    simpa only [zero_add] using (hp 0).symm
  let F : C(AddCircle T, ℂ) :=
    ⟨AddCircle.liftIco T 0 H,
      AddCircle.liftIco_zero_continuous he hc.continuousOn⟩
  have hcoeffF : ∀ n : ℤ, q n=fourierCoeff F n := by
    intro n
    rw [hcoeff n]
    change fourierCoeffOn hT.out H n=fourierCoeff (AddCircle.liftIco T 0 H) n
    simpa only [zero_add] using (fourierCoeff_liftIco_eq (T := T) (a := 0) H n).symm
  calc
    (∑' n : ℤ, q n) = F 0 := horizontal_fourier_sum_at_zero F hq hcoeffF
    _ = H 0 := by
      change AddCircle.liftIco T 0 H ((0:ℝ):AddCircle T)=H 0
      exact AddCircle.liftIco_zero_coe_apply ⟨le_rfl,hT.out⟩

end
end IsingBulk.HT.Final
