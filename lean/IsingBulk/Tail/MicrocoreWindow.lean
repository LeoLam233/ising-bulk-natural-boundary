import IsingBulk.Tail.MicrocoreGap
import IsingBulk.Tail.IntermediateWindow

/-! The source exponential microcore scale and its uniform resultant-gap
smallness, proved with the threshold before every particle number. -/
namespace IsingBulk.Tail
noncomputable section
open Filter
open scoped Topology BigOperators

def microcoreRadius (A c : ℝ) (N : ℕ) : ℝ :=
  c*Real.exp (-(A+4)*N)/(N:ℝ)

theorem microcore_radius_budget (A c : ℝ) (_hc : 0 ≤ c) (hcsmall : c ≤ 1/4)
    (N : ℕ) (hN : 1 ≤ N) :
    (N:ℝ)*microcoreRadius A c N ≤ Real.exp (-A*N)/4 := by
  have hn : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  unfold microcoreRadius
  rw [mul_div_cancel₀ _ hn.ne']
  have he : Real.exp (-(A+4)*N) ≤ Real.exp (-A*N) :=
    Real.exp_le_exp.mpr (by nlinarith)
  calc
    c*Real.exp (-(A+4)*N) ≤ (1/4:ℝ)*Real.exp (-A*N) :=
      mul_le_mul hcsmall he (Real.exp_pos _).le (by norm_num)
    _ = _ := by ring

theorem microcore_window_budget (D A c₀ c : ℝ) (hD : 0 ≤ D) (hA : 0 ≤ A)
    (hc₀ : 0 < c₀) (hc : 0 ≤ c) (hcsmall : c ≤ 1/4) :
    ∀ᶠ H : ℝ in atTop, ∀ N : ℕ, 1 ≤ N → (N:ℝ) ≤ D*Real.sqrt H →
      (N:ℝ)*(c₀*Real.exp (-H)+microcoreRadius A c N) ≤ Real.exp (-A*N)/2 := by
  have hb : 0 < 1/(4*c₀) := by positivity
  filter_upwards [intermediate_window_uniform_small D A 1 1 hD hA zero_lt_one
    (1/(4*c₀)) hb] with H hH
  intro N hN hwindow
  have hsmall := (hH N hwindow).le
  simp only [one_mul,neg_mul,pow_one] at hsmall
  have hmul := mul_le_mul_of_nonneg_left hsmall
    (show 0 ≤ c₀*Real.exp (-A*N) by positivity)
  have he : Real.exp (-A*N)*Real.exp (A*N)=1 := by rw [← Real.exp_add]; simp
  have hleft : c₀*Real.exp (-A*N)*(Real.exp (-H)*Real.exp (A*N)*(N:ℝ)) =
      (N:ℝ)*c₀*Real.exp (-H) := by
    calc
      _ = (N:ℝ)*c₀*Real.exp (-H)*(Real.exp (-A*N)*Real.exp (A*N)) := by ring
      _ = _ := by rw [he,mul_one]
  rw [hleft] at hmul
  have hright : c₀*Real.exp (-A*N)*(1/(4*c₀))=Real.exp (-A*N)/4 := by
    field_simp
  rw [hright] at hmul
  have hrad := microcore_radius_budget A c hc hcsmall N hN
  nlinarith

/-- The actual source Y-gap in the whole intermediate window. One A and
one eventual H threshold precede every N and every supported microcore point. -/
theorem uniform_microcore_product_gap (b D c₀ c : ℝ)
    (halg : IsAlgebraic ℚ (Complex.exp (-(b:ℂ)*Complex.I)))
    (hnot : ∀ N : ℕ, 1 ≤ N → Complex.exp (-(b:ℂ)*Complex.I)^N ≠ 1)
    (hD : 0 ≤ D) (hc₀ : 0 < c₀) (hc : 0 < c) (hcsmall : c ≤ 1/4) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ H : ℝ in atTop,
      ∀ N : ℕ, 1 ≤ N → (N:ℝ) ≤ D*Real.sqrt H → ∀ u : Fin N → ℝ,
      (∀ i, |u i| ≤ microcoreRadius A c N) →
      Real.exp (-A*N)/2 ≤ ‖1-∏ i, microcoreY c₀ (Real.exp (-H)) b (u i)‖ := by
  obtain ⟨A,hA,hgap⟩ := algebraic_microcore_gap b halg hnot
  refine ⟨A,hA,?_⟩
  filter_upwards [microcore_window_budget D A c₀ c hD hA.le hc₀ hc.le hcsmall] with H hH
  intro N hN hwindow u hu
  exact hgap N hN u c₀ (Real.exp (-H)) (microcoreRadius A c N) hc₀.le
    (Real.exp_pos _).le hu (hH N hN hwindow)

 theorem microcoreRadius_pos (A c : ℝ) (hc : 0 < c) (N : ℕ) (hN : 1 ≤ N) :
    0 < microcoreRadius A c N := by
  unfold microcoreRadius
  have hn : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  positivity

 theorem microcoreRadius_le_prefactor (A c : ℝ) (hA : 0 ≤ A) (hc : 0 ≤ c)
    (N : ℕ) (hN : 1 ≤ N) : microcoreRadius A c N ≤ c := by
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  have he : Real.exp (-(A+4)*N) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  unfold microcoreRadius
  apply (div_le_iff₀ (by linarith : 0 < (N:ℝ))).mpr
  nlinarith

 theorem particle_sqrt_microcoreRadius_le (A c : ℝ) (hA : 0 ≤ A) (hc : 0 < c)
    (N : ℕ) (hN : 1 ≤ N) : (N:ℝ)*Real.sqrt (microcoreRadius A c N) ≤ Real.sqrt c := by
  have hn : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hNexp : (N:ℝ)*Real.exp (-(A+4)*N) ≤ 1 := by
    calc
      _ ≤ Real.exp (N:ℝ)*Real.exp (-(A+4)*N) :=
        mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (N:ℝ)]) (Real.exp_pos _).le
      _ = Real.exp (-(A+3)*N) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hsq : (N:ℝ)^2*microcoreRadius A c N ≤ c := by
    have he : (N:ℝ)^2*microcoreRadius A c N=c*((N:ℝ)*Real.exp (-(A+4)*N)) := by
      unfold microcoreRadius
      field_simp
    rw [he]
    exact mul_le_of_le_one_right hc.le hNexp
  have hh := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq hn.le] at hh
  exact hh

 theorem microcore_window_epsilon_le_radius (D A c : ℝ) (hD : 0 ≤ D)
    (hA : 0 ≤ A) (hc : 0 < c) :
    ∀ᶠ H : ℝ in atTop, ∀ N : ℕ, 1 ≤ N → (N:ℝ) ≤ D*Real.sqrt H →
      Real.exp (-H) ≤ microcoreRadius A c N := by
  filter_upwards [intermediate_window_uniform_small D (A+4) 1 1 hD (by linarith)
    zero_lt_one c hc] with H hH
  intro N hN hwindow
  have hn : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hb := (hH N hwindow).le
  simp only [one_mul,neg_mul,pow_one] at hb
  have hh := mul_le_mul_of_nonneg_left hb (Real.exp_pos (-(A+4)*N)).le
  have he : Real.exp (-(A+4)*N)*Real.exp ((A+4)*N)=1 := by
    rw [← Real.exp_add,show -(A+4)*(N:ℝ)+(A+4)*N=0 by ring,Real.exp_zero]
  have hl : Real.exp (-(A+4)*N)*(Real.exp (-H)*Real.exp ((A+4)*N)*(N:ℝ)) =
      Real.exp (-H)*(N:ℝ) := by
    calc
      _ = Real.exp (-H)*(N:ℝ)*(Real.exp (-(A+4)*N)*Real.exp ((A+4)*N)) := by ring
      _ = _ := by rw [he,mul_one]
  rw [hl] at hh
  unfold microcoreRadius
  exact (le_div_iff₀ hn).mpr (by simpa only [mul_comm] using hh)

end
end IsingBulk.Tail
