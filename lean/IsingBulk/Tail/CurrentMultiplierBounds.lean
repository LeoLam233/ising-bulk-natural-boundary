import IsingBulk.Tail.SelectorJacobianBounds
import IsingBulk.Tail.ProtectedDensity

/-! Fixed real Stokes multipliers cost one uniform constant per named term,
not an occupancy-dependent weight. -/
namespace IsingBulk.Tail
noncomputable section
open scoped BigOperators

theorem namedSelectorDerivative_abs_le {N : ℕ} (f : SelectorFunctions)
    {B : ℝ} (hB : 0 ≤ B) (ha : ∀ x, 0 ≤ f.a x ∧ f.a x ≤ 1)
    (hd : ∀ x, |deriv f.a x| ≤ B) (q : Fin N) (θ : Fin N → ℝ) :
    |namedSelectorDerivative f q θ| ≤ B := by
  classical
  have hp0 : 0 ≤ ∏ i ∈ Finset.univ.erase q, (1-f.a (θ i)) :=
    Finset.prod_nonneg (fun i _ => sub_nonneg.mpr (ha (θ i)).2)
  have hp1 : ∏ i ∈ Finset.univ.erase q, (1-f.a (θ i)) ≤ 1 :=
    Finset.prod_le_one₀ (fun i _ => sub_nonneg.mpr (ha (θ i)).2)
      (fun i _ => by linarith [(ha (θ i)).1])
  rw [namedSelectorDerivative,abs_mul,abs_neg,abs_of_nonneg hp0]
  exact (mul_le_mul_of_nonneg_right (hd (θ q)) hp0).trans
    (mul_le_of_le_one_right hB hp1)

theorem constructed_current_multiplier_bound (b η α τ : ℝ)
    (hb : 0 < Real.sin b) (hη : 0 < η) (hηsmall : η ≤ Real.sin b/4)
    (hα : 0 < α) (hτ : 0 < τ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (N : ℕ) (q : Fin N) (θ : Fin N → ℝ),
      ‖-2*Complex.I*(τ:ℂ)*(namedSelectorDerivative (constructedSelector b η α) q θ:ℂ)‖ ≤ B := by
  let f := constructedSelector b η α
  have hf := constructedSelector_regular b η α hb hη hηsmall hα
  have hd := (periodic_derivative hf.a_periodic).isBounded_of_continuous
    Real.two_pi_pos.ne' (hf.a_smooth.continuous_deriv (by simp))
  obtain ⟨D,hD,hbound⟩ := hd.exists_pos_norm_le
  refine ⟨2*τ*D,by positivity,?_⟩
  intro N q θ
  have hder : ∀ x, |deriv f.a x| ≤ D := fun x => by
    simpa only [Real.norm_eq_abs] using hbound (deriv f.a x) ⟨x,rfl⟩
  have hn := namedSelectorDerivative_abs_le f hD.le
    (fun x => thresholdStep_range _ _ _) hder q θ
  simpa only [norm_mul,norm_neg,Complex.norm_ofNat,Complex.norm_I,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos hτ,mul_one] using
    mul_le_mul_of_nonneg_left hn (show 0 ≤ 2*τ by positivity)

end
end IsingBulk.Tail
