import IsingBulk.Tail.CompactGuardedWeights

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Lie Set Filter
open scoped Topology ContDiff BigOperators
set_option maxHeartbeats 1800000

theorem compactPairWeight_selected_jets_gap_factor {N : ℕ} (P : Finset (Fin N × Fin N))
    (M L : ℕ) (hM : 0 < M) (p : ℂ × (Fin N → ℝ)) (d ρ T : ℝ)
    (hd : 0 < d) (hρ : 0 < ρ) (hρd : ρ ≤ d) (hT : 1 ≤ T)
    (hp : ∀ q ∈ P, |p.2 q.1-p.2 q.2| ≤ d) (hatt : ∃ q ∈ P, |p.2 q.1-p.2 q.2|=d)
    (i j : Fin N) (hsel : |p.2 i-p.2 j| ≤ T*ρ) :
    RealScaledJetBound (fun q : ℂ × (Fin N → ℝ) => (compactPairWeight P M i j q.2:ℂ))
      p L ρ (T^(2*M)*compactPairWeightJetConstant N M L*d^(-(2*M:ℕ):ℤ)) (2*M:ℕ) := by
  have hl := real_linear_scaled_jets (jointAngularDifference i j) p L ρ (2*T) hρ (by positivity)
    ((jointAngularDifference_norm i j).trans (by linarith)) (by
      rw [jointAngularDifference_apply,Complex.norm_real,Real.norm_eq_abs]
      nlinarith)
  have hn := hl.pow hρ (2*M) (by omega)
  have hi := (compactPairWeightDenom_inverse_jets P M L hM p d hd hp hatt).smaller_scale hd hρ hρd
  have hh := hn.mul hi hρ
  have he : 2^L*((2*T)^(2*M)*(2*M:ℕ)^L)*
      (((L.factorial:ℝ)^2*(max 1 ((N:ℝ)^2*(2^(2*M)*(2*M:ℕ)^L)))^L)*d^(-(2*M:ℕ):ℤ))=
        T^(2*M)*compactPairWeightJetConstant N M L*d^(-(2*M:ℕ):ℤ) := by
    unfold compactPairWeightJetConstant
    rw [mul_pow]
    ring
  rw [he] at hh
  simpa only [compactPairWeight,div_eq_mul_inv,Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_pow,
    jointAngularDifference_apply,one_mul,add_zero] using hh

/-- The angular cutoff may have any positive radius. Its constant G is
independent of that radius; all selected zeros survive until Lie steps use them. -/
theorem compact_guarded_weighted_lie_jets {n : ℕ} {Ω : Set (ℂ × AngularSpace n)}
    (hΩ : IsOpen Ω) (V : ℂ → AngularSpace n → Fin (n+1) → ℂ)
    (A : ℂ → AngularSpace n → ℂ) (P : Finset (Fin (n+1) × Fin (n+1)))
    (M L : ℕ) (hM : 0 < M) (i j : Fin (n+1)) (h : ℝ)
    (hV : ∀ l, ParameterSmoothOn Ω (fun s x => V s x l)) (hA : ParameterSmoothOn Ω A)
    (hden : ∀ q ∈ Ω, compactPairWeightDenom P M q.2 ≠ 0)
    {p : ℂ × AngularSpace n} (hpΩ : p ∈ Ω) {d ρ T B C G K : ℝ}
    (hd : 0 < d) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hρd : ρ ≤ d) (hT : 1 ≤ T) (hB : 0 ≤ B)
    (hK : 1+(n+1:ℕ)*2^L*B ≤ K)
    (hp : ∀ q ∈ P, |p.2 q.1-p.2 q.2| ≤ d) (hatt : ∃ q ∈ P, |p.2 q.1-p.2 q.2|=d)
    (hsel : |p.2 i-p.2 j| ≤ T*ρ)
    (hVb : ∀ l, RealScaledJetBound (fun q => V q.1 q.2 l) p L ρ B (-1))
    (hAb : RealScaledJetBound (Function.uncurry A) p L ρ C 0)
    (hgb : RealScaledJetBound (fun q : ℂ × AngularSpace n => (allBranchSelectedGuard h i j q.2:ℂ)) p L ρ G 0) :
    ∀ k ≤ L, RealScaledJetBound
      (Function.uncurry ((lieStep V)^[k] (fun s x => (compactGuardedPairWeight P M h i j x:ℂ)*A s x)))
      p (L-k) ρ
      ((2^(2*L)*T^(2*M)*compactPairWeightJetConstant (n+1) M L*G*C*d^(-(2*M:ℕ):ℤ))*K^k)
      ((2*M:ℕ)-2*(k:ℤ)) := by
  have hw := compactPairWeight_selected_jets_gap_factor P M L hM p d ρ T hd hρ hρd hT hp hatt i j hsel
  have hh := (hw.mul hgb hρ).mul hAb hρ
  simp only [add_zero] at hh
  have he : 2^L*(2^L*(T^(2*M)*compactPairWeightJetConstant (n+1) M L*d^(-(2*M:ℕ):ℤ))*G)*C=
      2^(2*L)*T^(2*M)*compactPairWeightJetConstant (n+1) M L*G*C*d^(-(2*M:ℕ):ℤ) := by
    rw [show 2*L=L+L by omega,pow_add]
    ring
  rw [he] at hh
  have hh' : RealScaledJetBound
      (Function.uncurry (fun s x => (compactGuardedPairWeight P M h i j x:ℂ)*A s x)) p L ρ
      (2^(2*L)*T^(2*M)*compactPairWeightJetConstant (n+1) M L*G*C*d^(-(2*M:ℕ):ℤ)) (2*M:ℕ) := by
    apply hh.congr
    exact Eventually.of_forall (fun q => by simp only [compactGuardedPairWeight,Complex.ofReal_mul]; rfl)
  have hwsm := (compactPairWeight_parameter_smooth P M i j hden).mul
    (ParameterSmoothOn.angular Ω _ (Complex.ofRealCLM.contDiff.comp (allBranchSelectedGuard_smooth h i j)))
  have hasm : ParameterSmoothOn Ω (fun s x => (compactGuardedPairWeight P M h i j x:ℂ)*A s x) := by
    simpa [compactGuardedPairWeight,Function.comp_def] using hwsm.mul hA
  exact realScaledJetBound_iterate_lieStep hΩ V _ hV hasm hpΩ hρ hρ1 hB hK hVb hh'

end
end IsingBulk.Tail
