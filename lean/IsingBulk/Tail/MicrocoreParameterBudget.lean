import IsingBulk.Tail.MicrocoreTermBudget

/-! Parameter-only jet budgets for the actual semantic microcore terms.
These permit one-variable Cauchy estimates without introducing phase derivatives. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets Filter
open scoped Topology

theorem jetBound_congr_eventually {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f g : E → ℂ} {z : E} {J : ℕ} {C : ℝ} (h : JetBound f z J C)
    (he : g =ᶠ[𝓝 z] f) : JetBound g z J C := by
  refine ⟨h.analytic.congr he.symm,h.nonneg,?_⟩
  intro j hj
  rw [(he.iteratedFDeriv ℂ j).self_of_nhds]
  exact h.bound j hj

theorem microParameterDerivative_parameter_jet {N : ℕ} (F : ℂ × (Fin N → ℂ) → ℂ)
    (s : ℂ) (φ : Fin N → ℂ) (J : ℕ) (C : ℝ)
    (hF : AnalyticAt ℂ F (s,φ)) (h : JetBound (fun t => F (t,φ)) s (J+1) C) :
    JetBound (fun t => microParameterDerivative F (t,φ)) s J C := by
  have he : (fun t => microParameterDerivative F (t,φ)) =ᶠ[𝓝 s]
      (fun t => fderiv ℂ (fun t => F (t,φ)) t (1:ℂ)) := by
    have hn : ∀ᶠ t in 𝓝 s, AnalyticAt ℂ F (t,φ) :=
      (continuousAt_id.prodMk continuousAt_const).eventually hF.eventually_analyticAt
    filter_upwards [hn] with t ht
    rw [microParameterDerivative_eq F (t,φ) ht.differentiableAt]
    exact (fderiv_apply_one_eq_deriv).symm
  exact jetBound_congr_eventually (h.direction (1:ℂ) (by norm_num)) he

theorem microcoreJetTerms_parameter_budget {N : ℕ} (F : ℂ × (Fin N → ℂ) → ℂ)
    (s : ℂ) (φ : Fin N → ℂ) (J j : ℕ) (hj : j ≤ J) (C D : ℝ) (hC : 1 ≤ C)
    (hF : AnalyticAt ℂ F (s,φ))
    (hAjoint : ∀ i, AnalyticAt ℂ (fun t : ℂ × (Fin N → ℂ) => regularA t.1 (t.2 i)) (s,φ))
    (hFjet : JetBound (fun t => F (t,φ)) s J D)
    (hA : ∀ i, JetBound (fun t => regularA t (φ i)) s J C) :
    ∀ T ∈ microcoreJetTerms F j,
      JetBound (fun t => T.regularPart (t,φ)) s (J-j) ((2^J*C)^j*D) := by
  induction j with
  | zero =>
    intro T hT
    have he : T=⟨[],F⟩ := by simpa only [microcoreJetTerms,List.mem_singleton] using hT
    subst T
    simpa using hFjet
  | succ j ih =>
    intro T hT
    obtain ⟨P,hP,hT⟩ := List.mem_flatMap.mp hT
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp hT
    have hPjet := ih (by omega) P hP
    have hC0 : 0 ≤ C := by linarith
    have hB : 1 ≤ (2:ℝ)^J*C := by
      have hp : 1 ≤ (2:ℝ)^J := one_le_pow₀ (by norm_num)
      nlinarith
    cases a with
    | none =>
      have he : J-j=(J-(j+1))+1 := by omega
      rw [he] at hPjet
      have hd := microParameterDerivative_parameter_jet P.regularPart s φ (J-(j+1)) _
        (microcoreJetTerms_analytic F j (s,φ) hF hAjoint P hP) hPjet
      apply hd.mono le_rfl
      rw [pow_succ]
      have hD0 : 0 ≤ (2^J*C)^j*D := hPjet.nonneg
      nlinarith
    | some i =>
      have ha := ((hA i).mono (show J-(j+1) ≤ J by omega) le_rfl).neg
      have hp := hPjet.mono (show J-(j+1) ≤ J-j by omega) le_rfl
      have hh := ha.mul hp
      apply hh.mono le_rfl
      have he : (2:ℝ)^(J-(j+1)) ≤ 2^J := pow_le_pow_right₀ (by norm_num) (by omega)
      have hD0 := hp.nonneg
      calc
        _ ≤ 2^J*C*((2^J*C)^j*D) := by gcongr
        _ = _ := by rw [pow_succ]; ring

end
end IsingBulk.Tail
