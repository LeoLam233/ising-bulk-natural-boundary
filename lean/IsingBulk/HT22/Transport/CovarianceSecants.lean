import IsingBulk.HT22.Transport.MixedCovariance
import IsingBulk.HT22.Transport.SecantProjection

/-! Integration-to-covariance theorem for the actual fixed-occupancy arc.
This isolates only general calculus; actual inverse sector/size conditions
are separate geometric proofs, not fields assumed by the terminal target. -/
namespace IsingBulk.HT22
noncomputable section
open Set
open scoped BigOperators

 theorem covariance_pair_secant_bound {f f' w : ℝ → ℂ} {a b κ η L : ℝ} {phase : ℂ}
    (hab : a≤b) (hκ : 0≤κ) (hηκ : η≤κ) (hphase : ‖phase‖≤1)
    (hderiv : ∀ x∈Icc a b, HasDerivAt f (f' x) x)
    (hcont : ContinuousOn f' (Icc a b))
    (hcone : ∀ x∈Icc a b, κ*‖f' x‖≤(phase*f' x).re)
    (hsize : ∀ x∈Icc a b, L≤(phase*f' x).re)
    (hw : ‖w b-w a-((b-a):ℝ)‖≤η*(b-a)) :
    (κ-η)*L*(b-a)^2 ≤ (phase*((w b-w a)*(f b-f a))).re := by
  have hc := secant_projected_cone hab hκ hderiv hcont hcone
  have hs := secant_projected_size hab hderiv hcont hsize
  have hn : (phase*(f b-f a)).re≤‖f b-f a‖ := by
    calc
      _ ≤ ‖phase*(f b-f a)‖ := Complex.re_le_norm _
      _ = ‖phase‖*‖f b-f a‖ := norm_mul _ _
      _ ≤ _ := by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hphase (norm_nonneg (f b-f a))
  exact projected_product_lower hphase (sub_nonneg.mpr hab) hηκ hw hc (hs.trans hn)

 theorem mixedCovariance_secant_bound {N : ℕ} (θ : Fin N → ℝ)
    (f f' w : ℝ → ℂ) (phase : ℂ) (a b κ η L : ℝ)
    (hθ : ∀ i, θ i∈Icc a b) (hκ : 0≤κ) (hηκ : η≤κ) (hphase : ‖phase‖≤1)
    (hderiv : ∀ x∈Icc a b, HasDerivAt f (f' x) x)
    (hcont : ContinuousOn f' (Icc a b))
    (hcone : ∀ x∈Icc a b, κ*‖f' x‖≤(phase*f' x).re)
    (hsize : ∀ x∈Icc a b, L≤(phase*f' x).re)
    (hw : ∀ x∈Icc a b, ∀ y∈Icc a b, x≤y →
      ‖w y-w x-((y-x):ℝ)‖≤η*(y-x)) :
    ((κ-η)*L)*((∑ i, ∑ l, (θ i-θ l)^2)/2) ≤
      (phase*mixedCovariance (fun i => w (θ i)) (fun i => f (θ i))).re := by
  apply mixedCovariance_projected_lower
  intro i l
  have hordered (i l : Fin N) (hil : θ i≤θ l) :
      (κ-η)*L*(θ l-θ i)^2 ≤
        (phase*((w (θ l)-w (θ i))*(f (θ l)-f (θ i)))).re := by
    have hsub : Icc (θ i) (θ l) ⊆ Icc a b := Icc_subset_Icc (hθ i).1 (hθ l).2
    exact covariance_pair_secant_bound hil hκ hηκ hphase
      (fun x hx => hderiv x (hsub hx)) (hcont.mono hsub)
      (fun x hx => hcone x (hsub hx)) (fun x hx => hsize x (hsub hx))
      (hw (θ i) (hθ i) (θ l) (hθ l) hil)
  rcases le_total (θ i) (θ l) with hil | hli
  · have hh := hordered i l hil
    convert hh using 1 <;> ring
  · exact hordered l i hli

end
end IsingBulk.HT22
