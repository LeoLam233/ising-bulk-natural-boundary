import IsingBulk.First.ComplementAuxiliaryJets
import IsingBulk.First.ComplementFiniteAuxiliary
import IsingBulk.First.ComplementRadialChartDecay

/-! The Rʲ parameter-derivative cost is absorbed by j additional integrations
by parts, yielding the actual integrable selected-factor auxiliary tail. -/
namespace IsingBulk.First
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff

theorem sourceAuxiliaryJet_tail_bound_of_decay {N : ℕ} (r : ℝ) (s : ℂ)
    (w : DoubleAngularVector N → ℝ) (J : Finset (SingularFactorIndex N)) (j : ℕ)
    (hs : s ≠ 0)
    (hden : ∀ u : DoubleAngularVector N, ∀ f ∈ Jᶜ,
      sourceFactorDenominator s (angleTuple r u.1) (angleTuple r u.2) f ≠ 0)
    (C : ℝ)
    (hdecay : ∀ η ∈ auxiliarySimplex J, ∀ t ∈ Icc (0:ℝ) 1, ∀ R : ℝ, 0 < R →
      ‖∫ u, sourceIBPAmplitude w J j ((r,s),(η,t)) u *
        Complex.exp ((R : ℂ) * sourceIBPPhase J ((r,s),(η,t)) u)‖ ≤
        R⁻¹^(Fintype.card J+j+1)*C)
    (ξ : J → ℝ) (hξ : ξ ∈ finiteAuxiliaryTail J) :
    ‖∫ u, sourceAuxiliaryJet r s w J j ξ u‖ ≤
      (finiteAuxiliaryRadius ξ)⁻¹^(Fintype.card J+1)*C := by
  let R := finiteAuxiliaryRadius ξ
  have hR1 : 1 ≤ R := hξ.2
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have hη : (fun f => ξ f/R) ∈ auxiliarySimplex J := normalized_auxiliary_mem_simplex ξ hξ.1 hR
  have ht : R⁻¹ ∈ Icc (0:ℝ) 1 := ⟨inv_nonneg.mpr hR.le, (inv_le_one₀ hR).mpr hR1⟩
  rw [integral_sourceAuxiliaryJet_normalize r s w J j ξ R hR.ne' hs hden,
    norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  calc
    _ ≤ R^j * (R⁻¹^(Fintype.card J+j+1)*C) :=
      mul_le_mul_of_nonneg_left (hdecay _ hη _ ht R hR) (pow_nonneg hR.le _)
    _ = _ := by
      rw [show Fintype.card J+j+1=j+(Fintype.card J+1) by omega, pow_add]
      have hcancel : R^j * R⁻¹^j = 1 := by rw [← mul_pow, mul_inv_cancel₀ hR.ne', one_pow]
      calc
        _ = (R^j * R⁻¹^j) * (R⁻¹^(Fintype.card J+1)*C) := by ring
        _ = _ := by rw [hcancel, one_mul]

/-- Actual source local-chart fixed-order derivatives have a uniform
integrable auxiliary tail along the selected radial approach. -/
theorem selected_radial_chart_auxiliary_tail {p : ℕ} {a b : ℤ}
    (hp : p.Prime) (hp11 : 11 ≤ p)
    (ha : PrimeFamily.Admissible p a) (hb : PrimeFamily.Admissible p b)
    (θ : ℝ) (hθ : 0 < Real.sin θ)
    (hS : sourceS (Complex.exp ((θ : ℂ)*Complex.I)) =
      ((2*PrimeFamily.cosineAverage p a b : ℝ) : ℂ))
    (u₀ : DoubleAngularVector (2*p))
    (hgood : ¬ selectedBadConfiguration a b (angleTuple 1 u₀.1) (angleTuple 1 u₀.2))
    (J : Finset (SingularFactorIndex (2*p)))
    (hJ : ∀ f, f ∈ J ↔ singularFactorActive (angleTuple 1 u₀.1) (angleTuple 1 u₀.2)
      (2*PrimeFamily.cosineAverage p a b) f) :
    ∃ γ ε₀ : ℝ, 0 < γ ∧ 0 < ε₀ ∧
      ∀ w : DoubleAngularVector (2*p) → ℝ, ContDiff ℝ ∞ w →
      tsupport w ⊆ Metric.closedBall u₀ γ → ∀ j : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      ∀ ξ ∈ finiteAuxiliaryTail J,
        ‖∫ u, sourceAuxiliaryJet (sourceRadialPair θ ε).1 (sourceRadialPair θ ε).2 w J j ξ u‖ ≤
          (finiteAuxiliaryRadius ξ)⁻¹^(Fintype.card J+1)*C := by
  obtain ⟨γ,e,hγ,he,hdecay⟩ := selected_radial_chart_decay hp hp11 ha hb θ hθ hS u₀ hgood J hJ
  obtain ⟨d,hd,_,hm⟩ := radial_disk_source_trace_margin hθ
  refine ⟨γ,min e (d/2),hγ,lt_min he (by positivity),?_⟩
  intro w hw hsupp j
  obtain ⟨C,hC,hbound⟩ := hdecay w hw hsupp j (Fintype.card J+j+1)
  refine ⟨C,hC,?_⟩
  intro ε hε hεmax ξ hξ
  have hεe : ε ∈ Icc 0 e := ⟨hε.le,hεmax.trans (min_le_left _ _)⟩
  have hεd : ε < d := hεmax.trans_lt ((min_le_right _ _).trans_lt (by linarith))
  have hmargin := (hm ε hε hεd (IsingBulk.Branch.radialParameter θ ε)
    (by simpa using mul_pos (show 0 < Real.sin θ/16 by positivity) hε)).2
  have hr : 0 < (sourceRadialPair θ ε).1 := Real.exp_pos _
  have hr1 : (sourceRadialPair θ ε).1 < 1 := by
    change Real.exp (-(Real.sin θ/4)*ε) < 1
    rw [Real.exp_lt_one_iff]
    exact mul_neg_of_neg_of_pos (by linarith) hε
  have hs : (sourceRadialPair θ ε).2 ≠ 0 := by
    unfold sourceRadialPair IsingBulk.Branch.radialParameter
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (by linarith)) (Complex.exp_ne_zero _)
  exact sourceAuxiliaryJet_tail_bound_of_decay _ _ w J j hs
    (fun u f _ => sourceFactorDenominator_ne_zero_of_damping (Nat.mul_pos (by omega) hp.pos)
      hr hr1 hmargin u f) C (hbound ε hεe) ξ hξ

end
end IsingBulk.First
