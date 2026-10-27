import IsingBulk.Preferred22.FirstPhysicalAnalytic
import IsingBulk.Preferred22.FirstRemainder
import IsingBulk.Preferred22.RadialLogImprovement

/-! The final FTC step for the exact full first-coefficient remainder.
All analytic hypotheses refer to, and are discharged for, the actual
physical coefficient and its normalized localized chart. Only the source
next-derivative logarithmic estimate is left as a premise here. -/
namespace IsingBulk.Preferred22
noncomputable section
set_option maxHeartbeats 1000000

theorem preferred_first_remainder_of_log_next {n : ℕ} (he : Even (n+1))
    (α : ℝ) (hα : 0<α) (hαπ : α<Real.pi/2)
    (ha : Complex.exp (-(n+1:ℂ)*(α:ℂ)*Complex.I)=1) :
    ∃ R : ℝ,0<R ∧ ∀ χ : IsingBulk.First.ShapeSpace n → ℂ,
      Continuous χ → (∀ x,χ x≠0 → ‖x‖<R) → ∀ k : ℕ,
      (∃ C ε₀ : ℝ,0<C ∧ 0<ε₀ ∧ ∀ ε : ℝ,0<ε → ε<ε₀ →
        ‖iteratedDeriv (k+1) (coefficient (n+1))
            ((1+(ε:ℂ))*Complex.exp ((α:ℂ)*Complex.I))-
          2*iteratedDeriv (k+1) (localizedPhysicalIntegral α χ)
            ((1+(ε:ℂ))*Complex.exp ((α:ℂ)*Complex.I))‖≤C*(1+|Real.log ε|)) →
      PreferredFirstRemainderBound α n k χ := by
  obtain ⟨R,hR,hlocal⟩ := preferred_localized_physical_analytic_radial he α hα hαπ ha
  refine ⟨R,hR,?_⟩
  intro χ hχ hsupp k hlog
  obtain ⟨C,ε₀,hC,hε₀,hbound⟩ := hlog
  let ζ := Complex.exp ((α:ℂ)*Complex.I)
  let F := fun s : ℂ => coefficient (n+1) s-2*localizedPhysicalIntegral α χ s
  let a := min R ε₀/2
  have ha0 : 0<a := by dsimp only [a]; positivity
  have haR : a<R := by
    have hh := min_le_left R ε₀
    dsimp only [a]
    linarith
  have haε : a<ε₀ := by
    have hh := min_le_right R ε₀
    dsimp only [a]
    linarith
  have hζ : ‖ζ‖=1 := Complex.norm_exp_ofReal_mul_I α
  have hCana (ε : ℝ) (hε : 0<ε) :
      AnalyticAt ℂ (coefficient (n+1)) ((1+(ε:ℂ))*ζ) :=
    coefficient_analyticAt (n+1) (radialPath_exterior hζ hε)
  have hIana (ε : ℝ) (hε : 0<ε) (hεa : ε≤a) :
      AnalyticAt ℂ (localizedPhysicalIntegral α χ) ((1+(ε:ℂ))*ζ) :=
    hlocal χ hχ hsupp ε hε (hεa.trans_lt haR)
  have hFana (ε : ℝ) (hε : 0<ε) (hεa : ε≤a) :
      AnalyticAt ℂ F ((1+(ε:ℂ))*ζ) :=
    (hCana ε hε).sub (analyticAt_const.mul (hIana ε hε hεa))
  have hjet (j : ℕ) (ε : ℝ) (hε : 0<ε) (hεa : ε≤a) :
      iteratedDeriv j F ((1+(ε:ℂ))*ζ)=
        iteratedDeriv j (coefficient (n+1)) ((1+(ε:ℂ))*ζ)-
          2*iteratedDeriv j (localizedPhysicalIntegral α χ) ((1+(ε:ℂ))*ζ) := by
    have hdouble : AnalyticAt ℂ (fun t : ℂ => (2:ℂ)*localizedPhysicalIntegral α χ t)
        ((1+(ε:ℂ))*ζ) := analyticAt_const.mul (hIana ε hε hεa)
    unfold F
    rw [iteratedDeriv_fun_sub (hCana ε hε).contDiffAt hdouble.contDiffAt,
      iteratedDeriv_const_mul_field]
  obtain ⟨M,hM,hMbound⟩ := preferred_radial_log_improvement hζ ha0 hC.le k hFana
    (fun ε hε hεa => by
      rw [hjet (k+1) ε hε hεa]
      exact hbound ε hε (hεa.trans_lt haε))
  refine ⟨M,a,hM,ha0,?_⟩
  intro ε hε hεa
  rw [←hjet k ε hε hεa.le]
  exact hMbound ε hε hεa.le

end
end IsingBulk.Preferred22
