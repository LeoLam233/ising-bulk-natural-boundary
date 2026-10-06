import IsingBulk.Tail.MicrocoreParameterBudget
import IsingBulk.Tail.MicrocoreAmplitudeBound

/-! Scalar parameter slices inherit the proved regular-coordinate jet bounds. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets

theorem jetBound_parameter_slice {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    (F : ℂ × G → ℂ) (s : ℂ) (φ : G) (J : ℕ) (C : ℝ)
    (h : JetBound F (s,φ) J C) : JetBound (fun t => F (t,φ)) s J C := by
  let L : ℂ →L[ℂ] ℂ × G := ContinuousLinearMap.inl ℂ ℂ G
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro t
    simp [L,Prod.norm_def]
  have ht : JetBound (fun z : ℂ × G => F (z+(0,φ))) (s,0) J C := by
    refine ⟨?_,h.nonneg,?_⟩
    · have ha : AnalyticAt ℂ F ((s,0)+(0,φ)) := by simpa using h.analytic
      exact AnalyticAt.comp (g := F) (f := fun z : ℂ × G => z+(0,φ))
        (x := (s,0)) ha (analyticAt_id.add analyticAt_const)
    · intro j hj
      rw [iteratedFDeriv_comp_add_right]
      simpa using h.bound j hj
  have hh := JetBound.comp L ht hL
  convert! hh using 1
  ext t
  simp [L]

theorem microcore_regularA_parameter_uniform (s₀ : ℂ) (c : ℝ) (hs : s₀ ≠ 0)
    (hS : s₀+s₀⁻¹=(1+c:ℂ)) (hc : |c|<1) (J : ℕ) :
    ∃ C r : ℝ, 1 ≤ C ∧ 0 < r ∧ ∀ s φ : ℂ, ‖s-s₀‖ < r → ‖φ‖ < r →
      JetBound (fun t => regularA t φ) s J C := by
  obtain ⟨C,r,hC,hr,hb⟩ := micro_factor_bounds_uniform s₀ c hs hS hc J
  refine ⟨C,r,hC,hr,?_⟩
  intro s φ hs' hφ
  have hh := (hb 1 s (fun _ => φ) hs' (fun _ => hφ)).scalar (0:Fin 1) (3:Fin 4)
  have hh' : JetBound (fun z : ℂ × ℂ => regularA z.1 z.2) (s,φ) J C := by
    convert! hh using 1
  exact jetBound_parameter_slice _ s φ J C hh'

end
end IsingBulk.Tail
