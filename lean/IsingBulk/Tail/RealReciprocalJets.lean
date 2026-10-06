import IsingBulk.Tail.RealScaledJetBounds
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars

namespace IsingBulk.Tail
noncomputable section
open Set Filter
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
set_option maxHeartbeats 1500000

theorem real_inverse_jet_norm {z : ℂ} (hz : z ≠ 0) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun w : ℂ => w⁻¹) z‖ = (k.factorial:ℝ)*(‖z‖⁻¹)^(k+1) := by
  have hc : ContDiffAt ℂ (k:ℕ∞ω) (fun w : ℂ => w⁻¹) z := contDiffAt_id.inv hz
  rw [← hc.restrictScalars_iteratedFDeriv (𝕜 := ℝ)]
  simp only [Function.comp_apply,ContinuousMultilinearMap.norm_restrictScalars,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv,iteratedDeriv_eq_iterate,iter_deriv_inv,
    norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,Complex.norm_natCast,norm_zpow]
  congr 1
  rw [show (-1-(k:ℤ)) = -((k+1:ℕ):ℤ) by omega,zpow_neg,zpow_natCast,inv_pow]

theorem smooth_composition_jet_bound (f : E → ℂ) (g : ℂ → ℂ) (x : E) (k : ℕ)
    (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g (f x)) (C D : ℝ)
    (hC : ∀ i ≤ k, ‖iteratedFDeriv ℝ i g (f x)‖ ≤ C)
    (hD : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℝ i f x‖ ≤ D^i) :
    ‖iteratedFDeriv ℝ k (g ∘ f) x‖ ≤ k.factorial*C*D^k := by
  have he := (hg.of_le (show (k:ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)
  obtain ⟨V,hV,hVo,hfx⟩ := eventually_nhds_iff.mp he
  have hfnear := (hf.of_le (show (k:ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)
  have hpre := hf.continuousAt.preimage_mem_nhds (hVo.mem_nhds hfx)
  obtain ⟨U,hU,hUo,hx⟩ := eventually_nhds_iff.mp (hfnear.and hpre)
  have hh := norm_iteratedFDerivWithin_comp_le
    (fun y hy => (hV y hy).contDiffWithinAt)
    (fun y hy => (hU y hy).1.contDiffWithinAt) (n := k) (by simp)
    hVo.uniqueDiffOn hUo.uniqueDiffOn (fun y hy => (hU y hy).2) hx
    (C := C) (D := D)
    (by simpa only [iteratedFDerivWithin_of_isOpen _ hVo hfx] using hC)
    (by simpa only [iteratedFDerivWithin_of_isOpen _ hUo hx] using hD)
  simpa only [iteratedFDerivWithin_of_isOpen _ hUo hx] using hh

theorem real_reciprocal_scaled_jets (f : E → ℂ) (x : E) (J : ℕ) (ρ c B : ℝ)
    (hf : ContDiffAt ℝ ∞ f x) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hc : 0 < c)
    (hgap : c*ρ ≤ ‖f x‖)
    (hb : ∀ k, 1 ≤ k → k ≤ J → ‖iteratedFDeriv ℝ k f x‖ ≤ B) :
    RealScaledJetBound (fun y => (f y)⁻¹) x J ρ
      ((J.factorial:ℝ)^2*(max 1 c⁻¹)^(J+1)*(max 1 B)^J) (-1) := by
  have hn : 0 < ‖f x‖ := (mul_pos hc hρ).trans_le hgap
  have hne : f x ≠ 0 := norm_pos_iff.mp hn
  let R := max 1 c⁻¹
  let D := max 1 B
  have hR : 1 ≤ R := le_max_left _ _
  have hD : 1 ≤ D := le_max_left _ _
  have hS : 1 ≤ ρ⁻¹ := (one_le_inv₀ hρ).mpr hρ1
  have hinv : ‖f x‖⁻¹ ≤ R*ρ⁻¹ := by
    calc
      _ ≤ (c*ρ)⁻¹ := inv_anti₀ (mul_pos hc hρ) hgap
      _ = c⁻¹*ρ⁻¹ := mul_inv_rev c ρ |>.trans (mul_comm _ _)
      _ ≤ R*ρ⁻¹ := mul_le_mul_of_nonneg_right (le_max_right _ _) (inv_nonneg.mpr hρ.le)
  refine ⟨hf.inv hne,by positivity,?_⟩
  intro k hk
  have houter (i : ℕ) (hi : i ≤ k) :
      ‖iteratedFDeriv ℝ i (fun z : ℂ => z⁻¹) (f x)‖ ≤
        (J.factorial:ℝ)*R^(J+1)*(ρ⁻¹)^(k+1) := by
    rw [real_inverse_jet_norm hne]
    calc
      _ ≤ (i.factorial:ℝ)*(R*ρ⁻¹)^(i+1) := by gcongr
      _ = (i.factorial:ℝ)*R^(i+1)*(ρ⁻¹)^(i+1) := by rw [mul_pow]; ring
      _ ≤ (J.factorial:ℝ)*R^(J+1)*(ρ⁻¹)^(k+1) := by
        apply mul_le_mul
        · apply mul_le_mul
          · exact_mod_cast Nat.factorial_le (hi.trans hk)
          · exact pow_le_pow_right₀ hR (by omega)
          · positivity
          · positivity
        · exact pow_le_pow_right₀ hS (by omega)
        · positivity
        · positivity
  have hinner (i : ℕ) (hi : 1 ≤ i) (hik : i ≤ k) :
      ‖iteratedFDeriv ℝ i f x‖ ≤ D^i :=
    (hb i hi (hik.trans hk)).trans ((le_max_right _ _).trans (le_self_pow₀ hD (by omega)))
  have hh := smooth_composition_jet_bound f (fun z => z⁻¹) x k hf (contDiffAt_id.inv hne)
    _ D houter hinner
  change ‖iteratedFDeriv ℝ k (fun y => (f y)⁻¹) x‖ ≤ _ at hh
  calc
    _ ≤ (k.factorial:ℝ)*((J.factorial:ℝ)*R^(J+1)*(ρ⁻¹)^(k+1))*D^k := hh
    _ ≤ (J.factorial:ℝ)*((J.factorial:ℝ)*R^(J+1)*(ρ⁻¹)^(k+1))*D^J := by
      gcongr
    _ = _ := by
      have he : (ρ⁻¹)^(k+1)=ρ^(-1-(k:ℤ)) := by
        rw [show (-1-(k:ℤ)) = -((k+1:ℕ):ℤ) by omega,zpow_neg,zpow_natCast,inv_pow]
      rw [he]
      dsimp [R,D]
      ring

end
end IsingBulk.Tail
