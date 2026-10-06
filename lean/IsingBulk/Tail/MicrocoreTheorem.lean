import IsingBulk.Tail.MicrocoreDerivativeBound
import IsingBulk.Tail.MicrocoreSummability
import IsingBulk.Tail.SelectedBranchData

/-! Source-facing nonresonant microcore bound, literal selected family,
fixed cutoff scale before ε,N, and a summable cubic-decay majorant. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch IsingBulk.PrimeFamily Filter
open scoped Topology

theorem microcore_sqrt_power_eq_rpow (b : ℝ) (hb : 0 ≤ b) (N : ℕ) (hN : 1 ≤ N) :
    (Real.sqrt b)^(N^2-1)=b^(((N:ℝ)^2-1)/2) := by
  rw [Real.sqrt_eq_rpow,← Real.rpow_mul_natCast hb]
  congr 1
  have hN2 : 1 ≤ N^2 := by nlinarith
  rw [Nat.cast_sub hN2,Nat.cast_pow,Nat.cast_one]
  ring

def microcoreMajorant (A c E : ℝ) (N : ℕ) : ℝ :=
  Real.exp (E*(N:ℝ)^2)*(Real.sqrt (microcoreRadius A c N))^(N^2-1)

theorem microcoreMajorant_summable (A c E : ℝ) (hA : 0 ≤ A) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    Summable (microcoreMajorant A c E) := by
  have ha : 0 < (A+4)/2 := by linarith
  have hs := microcore_cubic_nat_exponent_summable E ((A+4)/2) ha
  apply hs.of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
  have hb := microcore_cubic_exponential_budget (A := A) hc hc1 N hN E
  have he : E*(N:ℝ)^2-(A+4)*(N:ℝ)*((N^2-1:ℕ):ℝ)/2=
      E*(N:ℝ)^2-((A+4)/2)*(N:ℝ)*((N^2-1:ℕ):ℝ) := by ring
  rw [he] at hb
  simpa only [microcoreMajorant,Real.norm_eq_abs,abs_of_nonneg (by positivity :
    0 ≤ Real.exp (E*(N:ℝ)^2)*(Real.sqrt (microcoreRadius A c N))^(N^2-1))] using hb

/-- Manuscript prop:micro with actual source normalization and exact rpow
exponent. The same constants handle every j≤J and every N in the window. -/
theorem nonresonant_microcore (d : LocalBranchData)
    (halg : IsAlgebraic ℚ (Complex.exp (-(d.thetaB:ℂ)*Complex.I)))
    (hnot : ∀ N : ℕ, 1 ≤ N → Complex.exp (-(d.thetaB:ℂ)*Complex.I)^N ≠ 1)
    (cap : ℝ) (hcap : 0 < cap) (J : ℕ) (D : ℝ) (hD : 0 ≤ D) :
    ∃ A c E : ℝ, 0 < A ∧ 0 < c ∧ c ≤ 1/4 ∧ c ≤ cap ∧ 0 < E ∧
      Summable (microcoreMajorant A c E) ∧
      ∀ᶠ H : ℝ in atTop, ∀ n : ℕ, ((n+2:ℕ):ℝ) ≤ D*Real.sqrt H →
        let ε := Real.exp (-H)
        let b := microcoreRadius A c (n+2)
        ∀ j ≤ J,
          ‖iteratedDeriv j (originalMicrocoreIntegral n d ε b) (radialParameter d.theta ε)‖ ≤
            Real.exp (E*((n+2:ℕ):ℝ)^2)*b^((((n+2:ℕ):ℝ)^2-1)/2) := by
  obtain ⟨A,c,E,hA,hc,hcs,hcap',hE,hbound⟩ := original_microcore_derivative_bound d halg hnot cap hcap J D hD
  refine ⟨A,c,E,hA,hc,hcs,hcap',hE,microcoreMajorant_summable A c E hA.le hc.le (by linarith),?_⟩
  filter_upwards [hbound] with H hH
  intro n hwindow
  dsimp only
  intro j hj
  have hh := hH n hwindow j hj
  rw [microcore_sqrt_power_eq_rpow _ (microcoreRadius_pos A c hc (n+2) (by omega)).le (n+2) (by omega)] at hh
  exact hh

/-- All algebraicity and nonresonance hypotheses are discharged for the
literal FIRST selected prime family; the original radius is sin(theta)/4. -/
theorem selected_nonresonant_microcore {p : ℕ} (hp : p.Prime) {a b : ℤ}
    (ha : Admissible p a) (hb : Admissible p b) (τ α : ℝ) (hτ : 0 < τ) (hα : 0 < α)
    (cap : ℝ) (hcap : 0 < cap) (J : ℕ) (D : ℝ) (hD : 0 ≤ D) :
    let d := selectedLocalBranchData ha hb τ α hτ hα
    ∃ A c E : ℝ, 0 < A ∧ 0 < c ∧ c ≤ 1/4 ∧ c ≤ cap ∧ 0 < E ∧
      Summable (microcoreMajorant A c E) ∧
      ∀ᶠ H : ℝ in atTop, ∀ n : ℕ, ((n+2:ℕ):ℝ) ≤ D*Real.sqrt H →
        let ε := Real.exp (-H)
        let bN := microcoreRadius A c (n+2)
        ∀ j ≤ J,
          ‖iteratedDeriv j (originalMicrocoreIntegral n d ε bN) (radialParameter d.theta ε)‖ ≤
            Real.exp (E*((n+2:ℕ):ℝ)^2)*bN^((((n+2:ℕ):ℝ)^2-1)/2) := by
  let d := selectedLocalBranchData ha hb τ α hτ hα
  apply nonresonant_microcore d _ _ cap hcap J D hD
  · exact selectedBranch_algebraic hp ha hb
  · intro N hN he
    apply selectedBranch_not_isOfFinOrder hp ha hb
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨N,by omega,he⟩

end
end IsingBulk.Tail
