import IsingBulk.Tail.MixedSourceNormalization

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets Set Filter
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

/-- Finite-jet estimate for the literal source density, with the two
integrable kernels and all branch-volume factors exposed. -/
theorem mixed_actual_density_jet_bound {n : ℕ}
    (J : Finset (Fin (n+1))) (j q : Fin (n+1)) (hj : j∈J) (hq : q∉J)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ) (θ : Fin (n+1) → ℝ)
    (hp_smooth : ContDiff ℝ ∞ f.p) (hm_smooth : ContDiff ℝ ∞ f.m)
    (hΩ : (s,θ)∈mixedSeparatedDomain J j q f r τ lam)
    (hbranch : ∀ i∈J,Real.sin (θ i)<0)
    (hp : ∀ i∈insert q J,f.p =ᶠ[𝓝 (θ i)] (fun _ => f.p (θ i)))
    (hm : ∀ i∈insert q J,f.m =ᶠ[𝓝 (θ i)] (fun _ => f.m (θ i)))
    (order k : ℕ) (hk : k≤order) (A B D : ℝ) (hA : 1≤A)
    (hR₁ : JetBound (mixedActiveBranchResidual J j q s
      (fun i => mixedContourPhase f r τ lam s θ i) (deformedPoint f r τ lam θ)) 0 (order+1) A)
    (hR₂ : JetBound (mixedActiveCompactResidual J j q s
      (fun i => mixedContourPhase f r τ lam s θ i) (deformedPoint f r τ lam θ)) 0 (order+1) A)
    (hV : ∀ i,JetBound (mixedActiveAngularVelocity J j q s
      (fun i => mixedContourPhase f r τ lam s θ i) (deformedPoint f r τ lam θ) i) 0 order A)
    (hF : JetBound (mixedActiveRegularAmplitude J q s
      (fun i => mixedContourPhase f r τ lam s θ i) (deformedPoint f r τ lam θ)) 0 order D)
    (w : (Fin (n+1) → ℝ) → ℝ) (hw : ContDiff ℝ ∞ w)
    (hcut : ∀ l : List (Fin (n+1)),l.length≤k → |cutoffJet l w θ|≤B) :
    ‖((IsingBulk.Lie.lieStep (mixedContourVelocity J j q f r τ lam))^[k]
      (fun z a => (w a:ℂ)*pulledDensity f r τ lam z a)) s θ‖ ≤
    ((n+1+1:ℕ):ℝ)^k*(B*‖mixedDensityNormalization f τ lam θ‖*
      ‖mixedSimpleKernel f r τ lam s θ‖*‖mixedHybridVolume J f r τ lam s θ‖*
      ((1+4*2^order*A)^k*D)) := by
  rw [mixed_actual_density_all_order J j q hj hq f hr τ lam s θ hp_smooth hm_smooth
    hΩ hbranch hp hm hR₁.analytic hR₂.analytic (fun i => (hV i).analytic) hF.analytic w hw k]
  exact mixedDensityJetTerms_pointwise_budget J j q f r τ lam s θ
    (mixedDensityNormalization f τ lam θ) w _ _ _ _ order k hk A B D hA hR₁ hR₂ hV hF hcut

/-- The finite expansion contributes only a power of particle number;
the source Gaussian coefficient is unchanged at every finite order. -/
theorem mixed_density_budget_gaussian {N order k : ℕ} (hN : 1≤N) (hk : k≤order)
    {C B H D K G : ℝ} (hC : 1≤C) (hB : 0≤B) (hH : 0≤H) (hD : 0≤D)
    (hK : 0≤K) (hG : 0≤G) :
    ((N+1:ℕ):ℝ)^k*(B^N*H^N*K*((1+4*2^order*((N:ℝ)*C))^k*
      (D^N*(N:ℝ)^(3*order)*G))) ≤
    ((2*(1+4*2^order*C))^order*B*H*D)^N*(N:ℝ)^(5*order)*G*K := by
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  have hn0 : (0:ℝ)≤N := Nat.cast_nonneg N
  let P : ℝ := 1+4*2^order*C
  have hC0 : 0≤C := zero_le_one.trans hC
  have hP : 1≤P := by dsimp [P]; linarith [show 0≤4*(2:ℝ)^order*C by positivity]
  have hP0 : 0≤P := zero_le_one.trans hP
  have hNP : 1≤(N:ℝ)*P := one_le_mul_of_one_le_of_one_le hn hP
  have hp : 1+4*2^order*((N:ℝ)*C)≤(N:ℝ)*P := by dsimp [P]; nlinarith
  have hk₁ : ((N+1:ℕ):ℝ)^k≤(2*(N:ℝ))^order := by
    calc
      _ ≤ (2*(N:ℝ))^k := pow_le_pow_left₀ (Nat.cast_nonneg _) (by push_cast; linarith) k
      _ ≤ _ := pow_le_pow_right₀ (by linarith) hk
  have hk₂ : (1+4*2^order*((N:ℝ)*C))^k≤((N:ℝ)*P)^order :=
    (pow_le_pow_left₀ (by positivity) hp k).trans (pow_le_pow_right₀ hNP hk)
  let Q := (2*P)^order
  have hQ : 1≤Q := one_le_pow₀ (by dsimp [P]; nlinarith [show 0≤(2:ℝ)^order*C by positivity])
  have hQN : Q≤Q^N := by simpa only [pow_one] using pow_le_pow_right₀ hQ hN
  calc
    _ ≤ (2*(N:ℝ))^order*(B^N*H^N*K*(((N:ℝ)*P)^order*(D^N*(N:ℝ)^(3*order)*G))) := by gcongr
    _ = Q*(B*H*D)^N*(N:ℝ)^(5*order)*G*K := by
      dsimp [Q]
      simp only [mul_pow,show 3*order=order*3 by omega,show 5*order=order*5 by omega,pow_mul]
      ring
    _ ≤ Q^N*(B*H*D)^N*(N:ℝ)^(5*order)*G*K := by gcongr
    _ = _ := by dsimp [Q,P]; simp only [mul_pow]; ring

/-- Gaussian bound for the actual Lie iterate. The coefficient hypotheses
are supplied by the internal original/current source jet families. -/
theorem mixed_actual_density_gaussian_bound {n : ℕ}
    (J : Finset (Fin (n+1))) (j q : Fin (n+1)) (hj : j∈J) (hq : q∉J)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ) (θ : Fin (n+1) → ℝ)
    (hp_smooth : ContDiff ℝ ∞ f.p) (hm_smooth : ContDiff ℝ ∞ f.m)
    (hΩ : (s,θ)∈mixedSeparatedDomain J j q f r τ lam)
    (hbranch : ∀ i∈J,Real.sin (θ i)<0)
    (hp : ∀ i∈insert q J,f.p =ᶠ[𝓝 (θ i)] (fun _ => f.p (θ i)))
    (hm : ∀ i∈insert q J,f.m =ᶠ[𝓝 (θ i)] (fun _ => f.m (θ i)))
    (order k : ℕ) (hk : k≤order) (A B H D κ : ℝ) (hA : 1≤A)
    (hB : 0≤B) (hH : 0≤H) (hD : 0≤D)
    (hR₁ : JetBound (mixedActiveBranchResidual J j q s
      (fun i => mixedContourPhase f r τ lam s θ i) (deformedPoint f r τ lam θ)) 0 (order+1) (((n+1:ℕ):ℝ)*A))
    (hR₂ : JetBound (mixedActiveCompactResidual J j q s
      (fun i => mixedContourPhase f r τ lam s θ i) (deformedPoint f r τ lam θ)) 0 (order+1) (((n+1:ℕ):ℝ)*A))
    (hV : ∀ i,JetBound (mixedActiveAngularVelocity J j q s
      (fun i => mixedContourPhase f r τ lam s θ i) (deformedPoint f r τ lam θ) i) 0 order (((n+1:ℕ):ℝ)*A))
    (hF : JetBound (mixedActiveRegularAmplitude J q s
      (fun i => mixedContourPhase f r τ lam s θ i) (deformedPoint f r τ lam θ)) 0 order
      (D^(n+1)*((n+1:ℕ):ℝ)^(3*order)*Real.exp (-κ*((n+1:ℕ):ℝ)^2)))
    (hnorm : ‖mixedDensityNormalization f τ lam θ‖≤H^(n+1))
    (w : (Fin (n+1) → ℝ) → ℝ) (hw : ContDiff ℝ ∞ w)
    (hcut : ∀ l : List (Fin (n+1)),l.length≤k → |cutoffJet l w θ|≤B^(n+1)) :
    ‖((IsingBulk.Lie.lieStep (mixedContourVelocity J j q f r τ lam))^[k]
      (fun z a => (w a:ℂ)*pulledDensity f r τ lam z a)) s θ‖ ≤
    ((2*(1+4*2^order*A))^order*B*H*D)^(n+1)*((n+1:ℕ):ℝ)^(5*order)*
      Real.exp (-κ*((n+1:ℕ):ℝ)^2)*
      (‖mixedSimpleKernel f r τ lam s θ‖*‖mixedHybridVolume J f r τ lam s θ‖) := by
  have hNA : 1≤((n+1:ℕ):ℝ)*A :=
    one_le_mul_of_one_le_of_one_le (by exact_mod_cast Nat.le_add_left 1 n) hA
  have hh := mixed_actual_density_jet_bound J j q hj hq f hr τ lam s θ hp_smooth hm_smooth
    hΩ hbranch hp hm order k hk _ _ _ hNA hR₁ hR₂ hV hF w hw hcut
  apply hh.trans
  calc
    _ ≤ ((n+1+1:ℕ):ℝ)^k*(B^(n+1)*H^(n+1)*
      (‖mixedSimpleKernel f r τ lam s θ‖*‖mixedHybridVolume J f r τ lam s θ‖)*
      ((1+4*2^order*(((n+1:ℕ):ℝ)*A))^k*
      (D^(n+1)*((n+1:ℕ):ℝ)^(3*order)*Real.exp (-κ*((n+1:ℕ):ℝ)^2)))) := by
        simp only [mul_assoc]
        gcongr
    _ ≤ _ := mixed_density_budget_gaussian (by omega) hk hA hB hH hD (by positivity) (by positivity)

end
end IsingBulk.Tail
