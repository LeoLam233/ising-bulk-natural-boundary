import IsingBulk.Tail.RealReciprocalJets

/-! Homogeneous reciprocal jets. Normalizing the value scale before applying
the composition bound retains the full denominator degree at every order. -/
namespace IsingBulk.Tail
noncomputable section
open Set Filter
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
set_option maxHeartbeats 1500000

theorem RealScaledJetBound.constant_scale {f : E → ℂ} {x : E} {J : ℕ} {ρ C : ℝ} {a : ℤ}
    (h : RealScaledJetBound f x J ρ C a) (hρ : 0 < ρ) (b : ℤ) :
    RealScaledJetBound (fun y => (ρ^b:ℝ)*f y) x J ρ C (a+b) := by
  refine ⟨h.smooth.const_smul ((ρ^b:ℝ):ℂ),h.nonneg,?_⟩
  intro k hk
  change ‖iteratedFDeriv ℝ k (fun y => ((ρ^b:ℝ):ℂ) • f y) x‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' (h.smooth.of_le (show (k:ℕ∞ω) ≤ ∞ by simp)),
    norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (zpow_pos hρ _)]
  calc
    _ ≤ ρ^b*(C*ρ^(a-(k:ℤ))) := mul_le_mul_of_nonneg_left (h.bound k hk) (zpow_nonneg hρ.le _)
    _ = C*(ρ^b*ρ^(a-(k:ℤ))) := by ring
    _ = _ := by rw [← zpow_add₀ hρ.ne']; congr 2; ring

theorem real_inverse_outer_uniform (z : ℂ) (J : ℕ) (c : ℝ) (hc : 0 < c)
    (hgap : c ≤ ‖z‖) :
    ∀ k ≤ J, ‖iteratedFDeriv ℝ k (fun w : ℂ => w⁻¹) z‖ ≤
      (J.factorial:ℝ)*(max 1 c⁻¹)^(J+1) := by
  intro k hk
  have hz : z ≠ 0 := norm_pos_iff.mp (hc.trans_le hgap)
  have hinv : ‖z‖⁻¹ ≤ max 1 c⁻¹ := (inv_anti₀ hc hgap).trans (le_max_right _ _)
  rw [real_inverse_jet_norm hz]
  apply mul_le_mul
  · exact_mod_cast Nat.factorial_le hk
  · exact (pow_le_pow_left₀ (by positivity) hinv _).trans
      (pow_le_pow_right₀ (le_max_left _ _) (by omega))
  · positivity
  · positivity

theorem real_scaled_inverse_degree_zero {f : E → ℂ} {x : E} {J : ℕ} {ρ C c : ℝ}
    (h : RealScaledJetBound f x J ρ C 0) (hρ : 0 < ρ) (hc : 0 < c) (hgap : c ≤ ‖f x‖) :
    RealScaledJetBound (fun y => (f y)⁻¹) x J ρ
      ((J.factorial:ℝ)^2*(max 1 c⁻¹)^(J+1)*(max 1 C)^J) 0 := by
  have hne : f x ≠ 0 := norm_pos_iff.mp (hc.trans_le hgap)
  let D := max 1 C
  have hD : 1 ≤ D := le_max_left _ _
  refine ⟨h.smooth.inv hne,by positivity,?_⟩
  intro k hk
  have hinner : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℝ i f x‖ ≤ (D*ρ⁻¹)^i := by
    intro i hi hik
    have hh := h.bound i (hik.trans hk)
    have he : ρ^(0-(i:ℤ))=(ρ⁻¹)^i := by
      rw [zero_sub,zpow_neg,zpow_natCast,inv_pow]
    rw [he] at hh
    rw [mul_pow]
    have hDi : C ≤ D^i := (le_max_right 1 C).trans (le_self_pow₀ hD (by omega : i ≠ 0))
    exact hh.trans (mul_le_mul_of_nonneg_right hDi (by positivity))
  have hh := smooth_composition_jet_bound f (fun z => z⁻¹) x k h.smooth
    (contDiffAt_id.inv hne) _ (D*ρ⁻¹)
    (fun i hi => real_inverse_outer_uniform (f x) J c hc hgap i (hi.trans hk)) hinner
  change ‖iteratedFDeriv ℝ k (fun y => (f y)⁻¹) x‖ ≤ _ at hh
  rw [mul_pow] at hh
  calc
    _ ≤ (k.factorial:ℝ)*((J.factorial:ℝ)*(max 1 c⁻¹)^(J+1))*(D^k*(ρ⁻¹)^k) := hh
    _ ≤ (J.factorial:ℝ)*((J.factorial:ℝ)*(max 1 c⁻¹)^(J+1))*(D^J*(ρ⁻¹)^k) := by gcongr
    _ = _ := by simp only [zero_sub,zpow_neg,zpow_natCast,inv_pow]; dsimp [D]; ring

theorem RealScaledJetBound.inv {f : E → ℂ} {x : E} {J : ℕ} {ρ C c : ℝ} {a : ℤ}
    (h : RealScaledJetBound f x J ρ C a) (hρ : 0 < ρ) (hc : 0 < c)
    (hgap : c*ρ^a ≤ ‖f x‖) :
    RealScaledJetBound (fun y => (f y)⁻¹) x J ρ
      ((J.factorial:ℝ)^2*(max 1 c⁻¹)^(J+1)*(max 1 C)^J) (-a) := by
  have hn := h.constant_scale hρ (-a)
  rw [add_neg_cancel] at hn
  have hnorm : c ≤ ‖((ρ^(-a):ℝ):ℂ)*f x‖ := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (zpow_pos hρ _)]
    have hh := mul_le_mul_of_nonneg_left hgap (zpow_nonneg hρ.le (-a))
    have he : ρ^(-a)*(c*ρ^a)=c := by
      rw [mul_left_comm,← zpow_add₀ hρ.ne',neg_add_cancel,zpow_zero,mul_one]
    rwa [he] at hh
  have hi := (real_scaled_inverse_degree_zero hn hρ hc hnorm).constant_scale hρ (-a)
  simp only [zero_add] at hi
  apply hi.congr
  exact Eventually.of_forall (fun y => by
    have hcoeff : ((ρ^(-a):ℝ):ℂ) ≠ 0 := by exact_mod_cast (zpow_pos hρ (-a)).ne'
    change (f y)⁻¹=((ρ^(-a):ℝ):ℂ)*(((ρ^(-a):ℝ):ℂ)*f y)⁻¹
    rw [mul_inv_rev,mul_left_comm,mul_inv_cancel₀ hcoeff,mul_one])

end
end IsingBulk.Tail
