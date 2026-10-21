import IsingBulk.HT.Tail.SignedMixedLieTransfer

namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail IsingBulk.Jets IsingBulk.HT.Contour Set Filter
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem signed_mixed_actual_density_gaussian_bound (ζ : ℂ) (hζ : ‖ζ‖ = 1) {n : ℕ}
    (J : Finset (Fin (n+1))) (j q : Fin (n+1)) (hj : j∈J) (hq : q∉J)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ) (θ : Fin (n+1) → ℝ)
    (hp_smooth : ContDiff ℝ ∞ f.p) (hm_smooth : ContDiff ℝ ∞ f.m)
    (hY : ∀ x : Fin (n+1) → ℝ, ‖coordinateProduct (deformedPoint f r τ lam x)‖ < 1)
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
      (fun z a => (w a:ℂ)*signedPulledDensity ζ f r τ lam z a)) s θ‖ ≤
    ((2*(1+4*2^order*A))^order*B*H*D)^(n+1)*((n+1:ℕ):ℝ)^(5*order)*
      Real.exp (-κ*((n+1:ℕ):ℝ)^2)*
      (‖signedMixedSimpleKernel ζ f r τ lam s θ‖*‖mixedHybridVolume J f r τ lam s θ‖) := by
  have hh := mixed_actual_density_gaussian_bound J j q hj hq f hr τ lam s θ hp_smooth hm_smooth
    hΩ hbranch hp hm order k hk A B H D κ hA hB hH hD hR₁ hR₂ hV hF hnorm w hw hcut
  have ht := signed_mixed_iterate_norm_transfer ζ hζ J j q hj f hr τ lam hp_smooth hm_smooth hY
    (fun x => (w x:ℂ)) (Complex.ofRealCLM.contDiff.comp hw) s θ hΩ hp hm k
    (B := ((2*(1+4*2^order*A))^order*B*H*D)^(n+1)*((n+1:ℕ):ℝ)^(5*order)*
      Real.exp (-κ*((n+1:ℕ):ℝ)^2)*‖mixedHybridVolume J f r τ lam s θ‖)
    (hh.trans_eq (by ring))
  exact ht.trans_eq (by ring)

end
end IsingBulk.HT.Tail
