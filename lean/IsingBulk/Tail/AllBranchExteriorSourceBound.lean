import IsingBulk.Tail.AllBranchExteriorFiniteOrders

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch Filter
open scoped Topology

theorem summable_polynomial_source_envelope {S : ℕ → ℝ} (hs : Summable S)
    (hn : ∀ N, 0 ≤ S N) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → ∀ H : ℝ, 0 ≤ H →
      S N*(H+1)^2 ≤ Real.exp ((C:ℝ)*N*Real.log (N+1))*(H+N)^C := by
  let K : ℝ := 1+∑' N, S N
  have hNS (N : ℕ) : S N ≤ K := by
    have hh : S N ≤ ∑' i, S i := by
      simpa only [Finset.sum_singleton] using hs.sum_le_tsum {N} (fun i _ => hn i)
    dsimp [K]
    linarith
  obtain ⟨C,hC⟩ := exists_nat_ge (max 2 (K/Real.log 2))
  have hC2 : 2 ≤ C := by exact_mod_cast (le_max_left (2:ℝ) _).trans hC
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hKC : K ≤ (C:ℝ)*Real.log 2 :=
    (div_le_iff₀ hlog).mp ((le_max_right _ _).trans hC)
  have hKe : K ≤ Real.exp ((C:ℝ)*Real.log 2) := by
    linarith [Real.add_one_le_exp ((C:ℝ)*Real.log 2)]
  refine ⟨C,hC2,?_⟩
  intro N hN H hH
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hlogN : Real.log 2 ≤ Real.log ((N:ℝ)+1) := Real.log_le_log (by norm_num) (by linarith)
  have hlogN0 : 0 ≤ Real.log ((N:ℝ)+1) := hlog.le.trans hlogN
  have hphase : Real.log 2 ≤ (N:ℝ)*Real.log ((N:ℝ)+1) := by
    have hh := mul_le_mul_of_nonneg_right hNr hlogN0
    linarith
  have hcoeff : K ≤ Real.exp ((C:ℝ)*N*Real.log ((N:ℝ)+1)) := by
    apply hKe.trans
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hphase (Nat.cast_nonneg C (α := ℝ))
    nlinarith
  have hpow : (H+1)^2 ≤ (H+(N:ℝ))^C :=
    (pow_le_pow_left₀ (by linarith) (by linarith) 2).trans
      (pow_le_pow_right₀ (by linarith) hC2)
  exact mul_le_mul ((hNS N).trans hcoeff) hpow (sq_nonneg _) (Real.exp_pos _).le

/-- The displayed estimate of prop:allB for the literal angular complement.
The stronger summable majorant is retained separately for composition. -/
theorem proposition_allB (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) (hα : d.alpha < Real.sin d.thetaB/4)
    (p : ℕ) (hp : 1 ≤ p) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ η δ : ℝ, ∀ hδ : 0 < δ, δ ≤ δ₀ →
      ∀ A c : ℝ, 0 ≤ A → 0 < c → c ≤ 1 →
      ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, β₀ ≤ β →
      ∀ j : ℕ, j ≤ (2*p)^2/2-1 → ∃ C : ℕ, 2 ≤ C ∧
      ∀ D : ℝ, 0 ≤ D → ∀ᶠ H : ℝ in atTop, ∀ N : ℕ,
        2*p+2 ≤ N → (N:ℝ) < D*Real.sqrt H →
        allBranchExteriorAngularNorm N d η δ (Real.exp (-H))
          (allBranchMicroRadius A c N) (allBranchEqualityRadius β N) hδ j ≤
          Real.exp ((C:ℝ)*N*Real.log (N+1))*(H+N)^C := by
  obtain ⟨B⟩ := lemma_branch d
  obtain ⟨δ₀,hδ₀,hfinite⟩ := allBranchExterior_angular_window_finite B hcsmall hα ((2*p)^2/2-1)
  refine ⟨δ₀,hδ₀,?_⟩
  intro η δ hδ hδsmall A c hA hc hc1
  obtain ⟨β₀,hβ₀,hβall⟩ := hfinite η δ hδ hδsmall A c hA hc hc1
  refine ⟨β₀,hβ₀,?_⟩
  intro β hβ j hj
  obtain ⟨S,hs,hn,hwindow⟩ := hβall β hβ j hj
  obtain ⟨C,hC,hsource⟩ := summable_polynomial_source_envelope hs hn
  refine ⟨C,hC,?_⟩
  intro D hD
  filter_upwards [hwindow D hD,eventually_ge_atTop (0:ℝ)] with H hbound hH
  intro N hN hNwin
  have hN1 : 1 ≤ N := by omega
  have hpred := Nat.sub_add_cancel hN1
  have hpreal : ((N-1:ℕ):ℝ)+1=N := by exact_mod_cast hpred
  have hdegree := allBranchExterior_source_degree hp hN hj
  have ho : 2*j+1 ≤ (N-1+1)*(N-1) := by rw [hpred]; omega
  have hh := hbound (N-1) (by rw [hpreal]; exact hNwin.le) ho
  simp only [hpred] at hh
  exact hh.trans (hsource N hN1 H hH)

end
end IsingBulk.Tail
