import IsingBulk.Preferred22.SourceCutoffFrameJets

/-! Fixed finite-particle smooth angular multipliers in the genuine
source frame. The real angular derivatives are bounded on the actual
compact one-sided box before they are transferred to the source frame. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set
open scoped BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

theorem preferred_smooth_compact_finite_jets {N : ℕ}
    (G : (Fin N → ℝ) → ℂ) (hG : ContDiff ℝ ∞ G)
    (K : Set (Fin N → ℝ)) (hK : IsCompact K) (j : ℕ) :
    ∃ A : ℝ,0<A ∧ ∀ k : ℕ,k≤j → ∀ θ∈K,‖iteratedFDeriv ℝ k G θ‖≤A := by
  have hb (k : ℕ) : ∃ A : ℝ,0<A ∧ ∀ θ∈K,‖iteratedFDeriv ℝ k G θ‖≤A := by
    obtain ⟨A,hA⟩ := hK.exists_bound_of_continuousOn
      (hG.continuous_iteratedFDeriv (by simp)).continuousOn
    refine ⟨|A|+1,by positivity,?_⟩
    intro θ hθ
    exact (hA θ hθ).trans (by linarith [le_abs_self A])
  choose A hA hAb using hb
  let M := 1+∑ k∈Finset.range (j+1),A k
  have hsum : 0≤∑ k∈Finset.range (j+1),A k := Finset.sum_nonneg (fun k _ => (hA k).le)
  refine ⟨M,by dsimp only [M]; linarith,?_⟩
  intro k hk θ hθ
  have hsingle := Finset.single_le_sum (fun i (_ : i∈Finset.range (j+1)) => (hA i).le)
    (show k∈Finset.range (j+1) by simpa only [Finset.mem_range] using Nat.lt_succ_of_le hk)
  exact (hAb k θ hθ).trans (by dsimp only [M]; linarith)

theorem preferred_actual_smooth_angular_frame_jets (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧
      ∀ B : PreferredCoareaBump d,B.delta<cap →
      ∃ ε₀ τ₀ δB : ℝ,0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
      ∀ N : ℕ,0<N → ∀ G : (Fin N → ℝ) → ℂ,ContDiff ℝ ∞ G →
      ∀ j : ℕ,∃ C : ℝ,0<C ∧
      ∀ ε τ : ℝ,0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
      ∀ θ : Fin N → ℝ,
      (∀ i,-δB≤θ i+d.b ∧ θ i+d.b≤d.b+B.delta) →
      ∀ xs : List (Option (Fin N)),xs.length≤j →
      ‖preferredFrameJet τ B.p B.m (fun _ x => G x) xs
        (IsingBulk.Branch.radialParameter d.alpha ε) θ‖≤C := by
  obtain ⟨cap,hcap,hcapa,hcontrol⟩ := preferred_actual_angular_frame_control d
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hBcap
  obtain ⟨ε₀,τ₀,δB,hε₀,hτ₀,hδB,hδBB,hbound⟩ := hcontrol B hBcap
  refine ⟨ε₀,τ₀,δB,hε₀,hτ₀,hδB,hδBB,?_⟩
  intro N hN G hG j
  obtain ⟨CF,hCF,hframe⟩ := hbound j
  let K : Set (Fin N → ℝ) := pi univ (fun _ => Icc (-d.b-δB) B.delta)
  have hK : IsCompact K := isCompact_univ_pi (fun _ => isCompact_Icc)
  obtain ⟨A,hA,hAj⟩ := preferred_smooth_compact_finite_jets G hG K hK j
  have hNp : (0:ℝ)<N := by exact_mod_cast hN
  have hCFp : 0<CF := lt_of_lt_of_le zero_lt_one hCF
  refine ⟨CF*(N:ℝ)^(j*j+2*j)*A,by positivity,?_⟩
  intro ε τ hε hεr hτ hτr θ hθ xs hxs
  have hθK : θ∈K := by
    intro i _
    exact ⟨by linarith [(hθ i).1],by linarith [(hθ i).2]⟩
  exact (hframe N hN ε τ hε hεr hτ hτr θ hθ).2.2.2.2
    G hG A hA.le (fun k hk => hAj k hk θ hθK) xs hxs

end
end IsingBulk.Preferred22
