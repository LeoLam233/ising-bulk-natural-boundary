import IsingBulk.Joint.FormFactors.ActualFamilyLeadingPackage
import IsingBulk.Joint.FormFactors.ActualFamilyLeadingNegativePackage

namespace IsingBulk.Joint
noncomputable section
open Set Filter Metric FormFactors Anisotropic
open scoped Topology

/-- Actual implicit complex-ratio families are constructed from original
physical boundary geometry. Each conclusion uses ONE positive complex disk
for its full physical leading limits AND every mixed differentiated full-particle
tail. No family-existence, physical-side or uniform-estimate premise is assumed.
The explicit field statements mirror the proved mathematical exports. -/
structure JointRatioFamilyConclusion : Prop where
  positive_high : ∀ {b : ℝ} {z₀ lam₀ : ℂ}
    (_hK : (z₀,lam₀*z₀)∈closure highDomain) (_hp : p (z₀,lam₀*z₀)^2≠1)
    (_hS : S (z₀,lam₀*z₀)≠0) (_hB : 0<(transferB (z₀,lam₀*z₀)).im)
    (_hprime : b∈primePhaseCosines)
    (_he0 : Transverse.positiveParameter b (z₀,lam₀*z₀)=0)
    (_hd : deriv (fun z=>Transverse.positiveParameter b (z,lam₀*z)) z₀≠0),
    ∃F : ComplexRatioFamily (Transverse.positiveParameter (b:ℂ)) highPrefactor 1 z₀ lam₀,
    ∃ρ : ℝ,∃q k : ℕ,∃c : ℝ,0<ρ ∧ ρ≤F.radius ∧ 1≤q ∧
      2*k+1=(2*q+1)^2 ∧ 0<c ∧
      (∀lam∈closedBall lam₀ ρ,∀u : ℂ,‖u‖≤ρ →
        (F.coupling (u,lam)∈highDomain ↔ 0<u.im)) ∧
      (∀lam∈closedBall lam₀ ρ,c≤‖Transverse.positiveHighLeading (2*q) k b F.coupling lam‖) ∧
      (∀j≤k,TendstoUniformlyOn (fun (t : ℝ) lam=>(t^2) • iteratedDeriv j
        (fun u=>highNormalizedBulk (F.coupling (u,lam))) (Complex.I*(t:ℂ)^2))
        (fun lam=>if j=k then Transverse.positiveHighLeading (2*q) k b F.coupling lam else 0)
        (𝓝[>] (0:ℝ)) (closedBall lam₀ ρ)) ∧
      (∀M : ℝ,∀ᶠt : ℝ in 𝓝[>] 0,∀lam∈closedBall lam₀ ρ,
        M<‖iteratedDeriv k (fun u=>highNormalizedBulk (F.coupling (u,lam))) (Complex.I*(t:ℂ)^2)‖) ∧
      (∀j : ℕ,∃G : ℕ→ℝ,Summable G ∧ (∀m,0≤G m) ∧
        ∀lam∈closedBall lam₀ ρ,∀u : ℂ,‖u‖<ρ → 0<u.im → ∀m : ℕ,
          ‖iteratedFDeriv ℂ j (F.actualFamilyOddTerm (j+2+m)) (u,lam)‖≤G m)
  positive_low : ∀ {b : ℝ} {z₀ lam₀ : ℂ}
    (_hK : (z₀,lam₀*z₀)∈closure lowDomain) (_hp : p (z₀,lam₀*z₀)^2≠1)
    (_hS : S (z₀,lam₀*z₀)≠0) (_hB : 0<(transferB (z₀,lam₀*z₀)).im)
    (_hprime : b∈primePhaseCosines)
    (_he0 : Transverse.positiveParameter b (z₀,lam₀*z₀)=0)
    (_hd : deriv (fun z=>Transverse.positiveParameter b (z,lam₀*z)) z₀≠0),
    ∃F : ComplexRatioFamily (Transverse.positiveParameter (b:ℂ)) lowPrefactor 1 z₀ lam₀,
    ∃ρ : ℝ,∃q k : ℕ,∃c : ℝ,0<ρ ∧ ρ≤F.radius ∧
      2*(k+1)=(2*q+2)^2 ∧ 0<c ∧
      (∀lam∈closedBall lam₀ ρ,∀u : ℂ,‖u‖≤ρ →
        (F.coupling (u,lam)∈lowDomain ↔ 0<u.im)) ∧
      (∀lam∈closedBall lam₀ ρ,c≤‖Transverse.positiveLowLeading (2*q+1) k b F.coupling lam‖) ∧
      (∀j≤k,TendstoUniformlyOn (fun (t : ℝ) lam=>t • iteratedDeriv j
        (fun u=>lowNormalizedBulk (F.coupling (u,lam))) (Complex.I*(t:ℂ)^2))
        (fun lam=>if j=k then Transverse.positiveLowLeading (2*q+1) k b F.coupling lam else 0)
        (𝓝[>] (0:ℝ)) (closedBall lam₀ ρ)) ∧
      (∀M : ℝ,∀ᶠt : ℝ in 𝓝[>] 0,∀lam∈closedBall lam₀ ρ,
        M<‖iteratedDeriv k (fun u=>lowNormalizedBulk (F.coupling (u,lam))) (Complex.I*(t:ℂ)^2)‖) ∧
      (∀j : ℕ,∃G : ℕ→ℝ,Summable G ∧ (∀m,0≤G m) ∧
        ∀lam∈closedBall lam₀ ρ,∀u : ℂ,‖u‖<ρ → 0<u.im → ∀m : ℕ,
          ‖iteratedFDeriv ℂ j (F.actualFamilyEvenTerm (j+1+m)) (u,lam)‖≤G m)
  negative_even_low : ∀ {b : ℝ} {z₀ lam₀ : ℂ}
    (_hK : (z₀,lam₀*z₀)∈closure lowDomain) (_hp : p (z₀,lam₀*z₀)^2≠1)
    (_hS : S (z₀,lam₀*z₀)≠0) (_hB : (transferB (z₀,lam₀*z₀)).im<0)
    (_hprime : b∈primePhaseCosines)
    (_he0 : Transverse.negativeParameter b (z₀,lam₀*z₀)=0)
    (_hd : deriv (fun z=>Transverse.negativeParameter b (z,lam₀*z)) z₀≠0),
    ∃F : ComplexRatioFamily (Transverse.negativeParameter (b:ℂ)) lowPrefactor (-1) z₀ lam₀,
    ∃ρ : ℝ,∃q k : ℕ,∃c : ℝ,0<ρ ∧ ρ≤F.radius ∧
      2*(k+1)=(2*q+2)^2 ∧ 0<c ∧
      (∀lam∈closedBall lam₀ ρ,∀u : ℂ,‖u‖≤ρ →
        (F.coupling (u,lam)∈lowDomain ↔ 0<u.im)) ∧
      (∀lam∈closedBall lam₀ ρ,c≤‖Transverse.negativeEvenLowLeading (2*q+1) k b F.coupling lam‖) ∧
      (∀j≤k,TendstoUniformlyOn (fun (t : ℝ) lam=>t • iteratedDeriv j
        (fun u=>lowNormalizedBulk (F.coupling (u,lam))) (Complex.I*(t:ℂ)^2))
        (fun lam=>if j=k then Transverse.negativeEvenLowLeading (2*q+1) k b F.coupling lam else 0)
        (𝓝[>] (0:ℝ)) (closedBall lam₀ ρ)) ∧
      (∀M : ℝ,∀ᶠt : ℝ in 𝓝[>] 0,∀lam∈closedBall lam₀ ρ,
        M<‖iteratedDeriv k (fun u=>lowNormalizedBulk (F.coupling (u,lam))) (Complex.I*(t:ℂ)^2)‖) ∧
      (∀j : ℕ,∃G : ℕ→ℝ,Summable G ∧ (∀m,0≤G m) ∧
        ∀lam∈closedBall lam₀ ρ,∀u : ℂ,‖u‖<ρ → 0<u.im → ∀m : ℕ,
          ‖iteratedFDeriv ℂ j (F.actualNegativeFamilyEvenTerm (j+1+m)) (u,lam)‖≤G m)

theorem joint_ratio_family_conclusion : JointRatioFamilyConclusion where
  positive_high := @FormFactors.exists_positive_high_ratio_family_leading_and_mixed_tails
  positive_low := @FormFactors.exists_positive_low_ratio_family_leading_and_mixed_tails
  negative_even_low := @FormFactors.exists_negative_even_low_ratio_family_leading_and_mixed_tails

end
end IsingBulk.Joint
