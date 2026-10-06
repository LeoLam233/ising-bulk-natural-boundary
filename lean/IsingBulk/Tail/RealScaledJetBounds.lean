import IsingBulk.Tail.ScaledSmoothProductJets
import IsingBulk.Tail.ParameterSmoothLie

/-! Dimension-independent real jet calculus for the compact source. The
scale degree is an integer and is retained exactly through multiplication
and directional differentiation. No angular analytic continuation is used. -/
namespace IsingBulk.Tail
noncomputable section
open Filter
open scoped Topology ContDiff BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
set_option maxHeartbeats 1500000

structure RealScaledJetBound (f : E → ℂ) (x : E) (J : ℕ) (ρ C : ℝ) (a : ℤ) : Prop where
  smooth : ContDiffAt ℝ ∞ f x
  nonneg : 0 ≤ C
  bound : ∀ k ≤ J, ‖iteratedFDeriv ℝ k f x‖ ≤ C*ρ^(a-(k:ℤ))

theorem RealScaledJetBound.mono {f : E → ℂ} {x : E} {J K : ℕ} {ρ C D : ℝ} {a : ℤ}
    (h : RealScaledJetBound f x J ρ C a) (hρ : 0 < ρ) (hK : K ≤ J) (hCD : C ≤ D) :
    RealScaledJetBound f x K ρ D a :=
  ⟨h.smooth,h.nonneg.trans hCD,fun k hk => (h.bound k (hk.trans hK)).trans
    (mul_le_mul_of_nonneg_right hCD (zpow_nonneg hρ.le _))⟩

theorem RealScaledJetBound.congr {f g : E → ℂ} {x : E} {J : ℕ} {ρ C : ℝ} {a : ℤ}
    (h : RealScaledJetBound f x J ρ C a) (he : g =ᶠ[𝓝 x] f) :
    RealScaledJetBound g x J ρ C a := by
  refine ⟨h.smooth.congr_of_eventuallyEq he,h.nonneg,?_⟩
  intro k hk
  rw [(he.iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds]
  exact h.bound k hk

theorem RealScaledJetBound.add {f g : E → ℂ} {x : E} {J : ℕ} {ρ C D : ℝ} {a : ℤ}
    (hf : RealScaledJetBound f x J ρ C a) (hg : RealScaledJetBound g x J ρ D a) :
    RealScaledJetBound (fun y => f y+g y) x J ρ (C+D) a := by
  refine ⟨hf.smooth.add hg.smooth,add_nonneg hf.nonneg hg.nonneg,?_⟩
  intro k hk
  rw [fun_iteratedFDeriv_add_apply (hf.smooth.of_le (by simp)).contDiffWithinAt
    (hg.smooth.of_le (by simp)).contDiffWithinAt]
  exact (norm_add_le _ _).trans ((add_le_add (hf.bound k hk) (hg.bound k hk)).trans_eq (by ring))

theorem RealScaledJetBound.neg {f : E → ℂ} {x : E} {J : ℕ} {ρ C : ℝ} {a : ℤ}
    (h : RealScaledJetBound f x J ρ C a) :
    RealScaledJetBound (fun y => -f y) x J ρ C a := by
  refine ⟨h.smooth.neg,h.nonneg,?_⟩
  intro k hk
  change ‖iteratedFDeriv ℝ k (-f) x‖ ≤ _
  simpa only [iteratedFDeriv_neg_apply,norm_neg] using h.bound k hk

theorem RealScaledJetBound.sub {f g : E → ℂ} {x : E} {J : ℕ} {ρ C D : ℝ} {a : ℤ}
    (hf : RealScaledJetBound f x J ρ C a) (hg : RealScaledJetBound g x J ρ D a) :
    RealScaledJetBound (fun y => f y-g y) x J ρ (C+D) a := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

theorem RealScaledJetBound.mul {f g : E → ℂ} {x : E} {J : ℕ} {ρ C D : ℝ} {a b : ℤ}
    (hf : RealScaledJetBound f x J ρ C a) (hg : RealScaledJetBound g x J ρ D b) (hρ : 0 < ρ) :
    RealScaledJetBound (fun y => f y*g y) x J ρ (2^J*C*D) (a+b) := by
  refine ⟨hf.smooth.mul hg.smooth,by have := hf.nonneg; have := hg.nonneg; positivity,?_⟩
  intro k hk
  have hterm (i : ℕ) (hi : i ∈ Finset.range (k+1)) :
      (k.choose i:ℝ)*‖iteratedFDeriv ℝ i f x‖*‖iteratedFDeriv ℝ (k-i) g x‖ ≤
        (k.choose i:ℝ)*(C*D*ρ^(a+b-(k:ℤ))) := by
    have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have he : (a-(i:ℤ))+(b-((k-i:ℕ):ℤ))=a+b-(k:ℤ) := by omega
    calc
      _ ≤ (k.choose i:ℝ)*(C*ρ^(a-(i:ℤ)))*(D*ρ^(b-((k-i:ℕ):ℤ))) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (hf.bound i (hik.trans hk)) (by positivity)
        · exact hg.bound (k-i) ((Nat.sub_le _ _).trans hk)
        · exact norm_nonneg _
        · have := hf.nonneg; positivity
      _ = (k.choose i:ℝ)*(C*D*(ρ^(a-(i:ℤ))*ρ^(b-((k-i:ℕ):ℤ)))) := by ring
      _ = _ := by rw [← zpow_add₀ hρ.ne',he]
  calc
    _ ≤ ∑ i ∈ Finset.range (k+1), (k.choose i:ℝ)*‖iteratedFDeriv ℝ i f x‖*
        ‖iteratedFDeriv ℝ (k-i) g x‖ := smooth_two_factor_jet_bound f g x k hf.smooth hg.smooth
    _ ≤ ∑ i ∈ Finset.range (k+1), (k.choose i:ℝ)*(C*D*ρ^(a+b-(k:ℤ))) :=
      Finset.sum_le_sum hterm
    _ = (2:ℝ)^k*(C*D*ρ^(a+b-(k:ℤ))) := by
      rw [← Finset.sum_mul]
      congr 1
      exact_mod_cast Nat.sum_range_choose k
    _ ≤ (2:ℝ)^J*(C*D*ρ^(a+b-(k:ℤ))) := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num) hk)
      (mul_nonneg (mul_nonneg hf.nonneg hg.nonneg) (zpow_nonneg hρ.le _))
    _ = _ := by ring

theorem RealScaledJetBound.direction {f : E → ℂ} {x : E} {J : ℕ} {ρ C : ℝ} {a : ℤ}
    (h : RealScaledJetBound f x (J+1) ρ C a) (hρ : 0 < ρ) (v : E) (hv : ‖v‖ ≤ 1) :
    RealScaledJetBound (fun y => fderiv ℝ f y v) x J ρ C (a-1) := by
  have hDiff : ContDiffAt ℝ ∞ (fderiv ℝ f) x := h.smooth.fderiv_right (by simp)
  refine ⟨hDiff.clm_apply contDiffAt_const,h.nonneg,?_⟩
  intro k hk
  have hb := norm_iteratedFDeriv_clm_apply_const (c := v) (n := k) (N := ∞) hDiff (by simp)
  rw [norm_iteratedFDeriv_fderiv] at hb
  have hn : 0 ≤ C*ρ^(a-((k+1:ℕ):ℤ)) := mul_nonneg h.nonneg (zpow_nonneg hρ.le _)
  apply hb.trans
  calc
    _ ≤ ‖v‖*(C*ρ^(a-((k+1:ℕ):ℤ))) := mul_le_mul_of_nonneg_left
      (h.bound (k+1) (by omega)) (norm_nonneg _)
    _ ≤ C*ρ^(a-((k+1:ℕ):ℤ)) := mul_le_of_le_one_left hn hv
    _ = _ := by congr 2; omega

theorem RealScaledJetBound.lower_degree {f : E → ℂ} {x : E} {J : ℕ} {ρ C : ℝ} {a : ℤ}
    (h : RealScaledJetBound f x J ρ C a) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    RealScaledJetBound f x J ρ C (a-1) := by
  refine ⟨h.smooth,h.nonneg,?_⟩
  intro k hk
  apply (h.bound k hk).trans
  have he : a-(k:ℤ)=(a-1-(k:ℤ))+1 := by ring
  rw [he,zpow_add₀ hρ.ne',zpow_one,← mul_assoc]
  exact mul_le_of_le_one_right (mul_nonneg h.nonneg (zpow_nonneg hρ.le _)) hρ1

theorem RealScaledJetBound.sum {N : ℕ} {f : Fin N → E → ℂ} {x : E} {J : ℕ}
    {ρ C : ℝ} {a : ℤ} (h : ∀ i, RealScaledJetBound (f i) x J ρ C a) (hC : 0 ≤ C) :
    RealScaledJetBound (fun y => ∑ i, f i y) x J ρ ((N:ℝ)*C) a := by
  refine ⟨ContDiffAt.sum (fun i _ => (h i).smooth),by positivity,?_⟩
  intro k hk
  rw [iteratedFDeriv_fun_sum_apply (fun i _ => (h i).smooth.of_le (by simp))]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _i : Fin N, C*ρ^(a-(k:ℤ)) := Finset.sum_le_sum (fun i _ => (h i).bound k hk)
    _ = _ := by simp [mul_assoc]

theorem RealScaledJetBound.of_uniform {f : E → ℂ} {x : E} {J : ℕ} {ρ C : ℝ}
    (hf : ContDiffAt ℝ ∞ f x) (hC : 0 ≤ C) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hb : ∀ k ≤ J, ‖iteratedFDeriv ℝ k f x‖ ≤ C) :
    RealScaledJetBound f x J ρ C 0 := by
  refine ⟨hf,hC,?_⟩
  intro k hk
  apply (hb k hk).trans
  have hh : 1 ≤ (ρ⁻¹)^k := one_le_pow₀ ((one_le_inv₀ hρ).mpr hρ1)
  simpa only [zero_sub,zpow_neg,zpow_natCast,inv_pow] using le_mul_of_one_le_right hC hh

theorem RealScaledJetBound.rescale_zero {f : E → ℂ} {x : E} {J : ℕ} {ρ C : ℝ} {a : ℤ}
    (h : RealScaledJetBound f x J 1 C a) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    RealScaledJetBound f x J ρ C 0 :=
  RealScaledJetBound.of_uniform h.smooth h.nonneg hρ hρ1
    (fun k hk => by simpa using h.bound k hk)

theorem RealScaledJetBound.zero (x : E) (J : ℕ) (ρ C : ℝ) (a : ℤ)
    (hρ : 0 ≤ ρ) (hC : 0 ≤ C) : RealScaledJetBound (fun _ : E => (0:ℂ)) x J ρ C a := by
  refine ⟨contDiffAt_const,hC,?_⟩
  intro k hk
  simp only [iteratedFDeriv_fun_zero,Pi.zero_apply,norm_zero]
  exact mul_nonneg hC (zpow_nonneg hρ _)

theorem real_direction_uniform_jets {f : E → ℂ} {x : E} {J : ℕ} {C : ℝ}
    (hf : ContDiffAt ℝ ∞ f x) (hC : 0 ≤ C) (v : E) (hv : ‖v‖ ≤ 1)
    (hb : ∀ k, 1 ≤ k → k ≤ J+1 → ‖iteratedFDeriv ℝ k f x‖ ≤ C) :
    RealScaledJetBound (fun y => fderiv ℝ f y v) x J 1 C 0 := by
  have hd : ContDiffAt ℝ ∞ (fderiv ℝ f) x := hf.fderiv_right (by simp)
  refine ⟨hd.clm_apply contDiffAt_const,hC,?_⟩
  intro k hk
  simp only [one_zpow,mul_one]
  have hh := norm_iteratedFDeriv_clm_apply_const (c := v) (n := k) (N := ∞) hd (by simp)
  rw [norm_iteratedFDeriv_fderiv] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left (hb (k+1) (by omega) (by omega))
    (norm_nonneg v)).trans (mul_le_of_le_one_left hC hv))

end
end IsingBulk.Tail
