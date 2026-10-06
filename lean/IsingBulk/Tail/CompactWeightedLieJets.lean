import IsingBulk.Tail.CompactPairWeightJets
import IsingBulk.Tail.RealScaledLieBounds

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Lie Set Filter
open scoped Topology ContDiff BigOperators
set_option maxHeartbeats 1800000

def compactPairWeightJetConstant (N M J : ℕ) : ℝ :=
  2^J*(2^(2*M)*(2*M:ℕ)^J)*
    ((J.factorial:ℝ)^2*(max 1 ((N:ℝ)^2*(2^(2*M)*(2*M:ℕ)^J)))^J)

theorem compactPairWeight_parameter_smooth {N : ℕ} (P : Finset (Fin N × Fin N))
    (M : ℕ) (i j : Fin N) {Ω : Set (ℂ × (Fin N → ℝ))}
    (hden : ∀ p ∈ Ω, compactPairWeightDenom P M p.2 ≠ 0) :
    ParameterSmoothOn Ω (fun _ x => (compactPairWeight P M i j x:ℂ)) := by
  intro p hp
  constructor
  · have hn : ContDiff ℝ ∞ (fun q : ℂ × (Fin N → ℝ) => (q.2 i-q.2 j)^(2*M)) := by fun_prop
    have hd : ContDiff ℝ ∞ (fun q : ℂ × (Fin N → ℝ) => compactPairWeightDenom P M q.2) := by
      unfold compactPairWeightDenom
      fun_prop
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp p (hn.contDiffAt.div hd.contDiffAt (hden p hp))
  · exact differentiableAt_const _

/-- A rational selected-pair weight retains 2M selected zeros. A Lie order
uses two of them, independently of the full-collision degree of the density. -/
theorem compact_weighted_lie_jets {n : ℕ} {Ω : Set (ℂ × AngularSpace n)}
    (hΩ : IsOpen Ω) (V : ℂ → AngularSpace n → Fin (n+1) → ℂ)
    (A : ℂ → AngularSpace n → ℂ) (P : Finset (Fin (n+1) × Fin (n+1)))
    (M L : ℕ) (hM : 0 < M) (i j : Fin (n+1))
    (hV : ∀ l, ParameterSmoothOn Ω (fun s x => V s x l)) (hA : ParameterSmoothOn Ω A)
    (hden : ∀ q ∈ Ω, compactPairWeightDenom P M q.2 ≠ 0)
    {p : ℂ × AngularSpace n} (hpΩ : p ∈ Ω) {d ρ B C K : ℝ} {a : ℤ}
    (hd : 0 < d) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hρd : ρ ≤ d) (hB : 0 ≤ B)
    (hK : 1+(n+1:ℕ)*2^L*B ≤ K)
    (hp : ∀ q ∈ P, |p.2 q.1-p.2 q.2| ≤ d) (hatt : ∃ q ∈ P, |p.2 q.1-p.2 q.2|=d)
    (hsel : |p.2 i-p.2 j| ≤ ρ)
    (hVb : ∀ l, RealScaledJetBound (fun q => V q.1 q.2 l) p L ρ B (-1))
    (hAb : RealScaledJetBound (Function.uncurry A) p L d C a) :
    ∀ k ≤ L, RealScaledJetBound
      (Function.uncurry ((lieStep V)^[k] (fun s x => (compactPairWeight P M i j x:ℂ)*A s x)))
      p (L-k) ρ
      ((2^L*compactPairWeightJetConstant (n+1) M L*C*d^(a-(2*M:ℕ)))*K^k)
      ((2*M:ℕ)-2*(k:ℤ)) := by
  have hw := compactPairWeight_selected_jets P M L hM p d ρ hd hρ hρd hp hatt i j hsel
  have hw' : RealScaledJetBound (fun q : ℂ × AngularSpace n => (compactPairWeight P M i j q.2:ℂ))
      p L ρ (compactPairWeightJetConstant (n+1) M L*d^(-(2*M:ℕ):ℤ)) (2*M:ℕ) := by
    simpa only [compactPairWeightJetConstant,mul_assoc] using hw
  have hh := hw'.mul (hAb.smaller_scale hd hρ hρd) hρ
  have hconst : 2^L*(compactPairWeightJetConstant (n+1) M L*d^(-(2*M:ℕ):ℤ))*(C*d^a)=
      2^L*compactPairWeightJetConstant (n+1) M L*C*d^(a-(2*M:ℕ)) := by
    calc
      _ = (2^L*compactPairWeightJetConstant (n+1) M L*C)*(d^(-(2*M:ℕ):ℤ)*d^a) := by ring
      _ = _ := by rw [← zpow_add₀ hd.ne']; congr 2; ring
  rw [add_zero,hconst] at hh
  exact realScaledJetBound_iterate_lieStep hΩ V _ hV
    ((compactPairWeight_parameter_smooth P M i j hden).mul hA) hpΩ hρ hρ1 hB hK hVb hh

theorem RealScaledJetBound.absorb_selected_scale
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℂ} {x : E} {J : ℕ} {d ρ C : ℝ} {a b : ℤ}
    (h : RealScaledJetBound f x J ρ (C*d^a) b)
    (hd : 0 < d) (hρ : 0 ≤ ρ) (hρd : ρ ≤ d) (hb : 0 ≤ b) :
    ‖f x‖ ≤ C*d^(a+b) := by
  have hh := h.bound 0 (Nat.zero_le J)
  simp only [norm_iteratedFDeriv_zero,Nat.cast_zero,sub_zero] at hh
  calc
    _ ≤ (C*d^a)*ρ^b := hh
    _ ≤ (C*d^a)*d^b := mul_le_mul_of_nonneg_left (zpow_le_zpow_left₀ hb hρ hρd) h.nonneg
    _ = _ := by rw [mul_assoc,← zpow_add₀ hd.ne']

end
end IsingBulk.Tail
