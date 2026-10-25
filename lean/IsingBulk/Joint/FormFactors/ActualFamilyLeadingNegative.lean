import IsingBulk.Joint.FormFactors.ActualFamilyLeadingNegativeData
import IsingBulk.Joint.Transverse.FamilyNegativeEvenLeading
import IsingBulk.Anisotropic.Geometry.PrimeOrientation

/-! Actual negative-even LT complex-ratio asymptotics of the literal complete
physical susceptibility, including every integer particle weight and phase. -/
namespace IsingBulk.Joint.FormFactors
noncomputable section
open Set Filter Metric IsingBulk.Anisotropic
open scoped Topology

/-- Actual low-temperature counterpart. Every positive even particle order is
retained, and the zero-particle vacuum remains removed. -/
theorem negative_even_low_ratio_family_leading {b : ℝ} {z₀ lam₀ : ℂ}
    (F : ComplexRatioFamily (Transverse.negativeParameter (b:ℂ)) lowPrefactor (-1) z₀ lam₀)
    (hK : (z₀,lam₀*z₀)∈closure lowDomain) (hp : p (z₀,lam₀*z₀)^2≠1)
    (hS : S (z₀,lam₀*z₀)≠0) (hB : (transferB (z₀,lam₀*z₀)).im<0)
    (hb : |b|<1) (hprime : b∈primePhaseCosines) :
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
        M<‖iteratedDeriv k (fun u=>lowNormalizedBulk (F.coupling (u,lam))) (Complex.I*(t:ℂ)^2)‖) := by
  obtain ⟨ρ,hρ,hρF,hca,hfront,hSn,hpn,hBn,hn,hside⟩ := F.actual_negative_even_low_family_inputs hK hp hS hB hb
  obtain ⟨q,k,c,hcritical,hc,hlower,hlimits,hunbounded⟩ :=
    Transverse.negative_even_low_compact_family_leading F.coupling (isCompact_closedBall _ _) hca hfront hSn hpn
      (fun lam hl=>by simpa only [Complex.neg_im,neg_pos] using hBn lam hl) hb hprime hn
  exact ⟨ρ,q,k,c,hρ,hρF,hcritical,hc,hside,hlower,hlimits,hunbounded⟩


/-- The true additive negative ratio family and its complete physical asymptotics are constructed from the boundary data. -/
theorem exists_negative_even_low_ratio_family_leading {b : ℝ} {z₀ lam₀ : ℂ}
    (hK : (z₀,lam₀*z₀)∈closure lowDomain) (hp : p (z₀,lam₀*z₀)^2≠1)
    (hS : S (z₀,lam₀*z₀)≠0) (hB : (transferB (z₀,lam₀*z₀)).im<0)
    (hprime : b∈primePhaseCosines)
    (he0 : Transverse.negativeParameter b (z₀,lam₀*z₀)=0)
    (hd : deriv (fun z=>Transverse.negativeParameter b (z,lam₀*z)) z₀≠0) :
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
        M<‖iteratedDeriv k (fun u=>lowNormalizedBulk (F.coupling (u,lam))) (Complex.I*(t:ℂ)^2)‖) := by
  obtain ⟨F⟩ := negative_even_low_complex_ratio_family hK hp hS hB he0 hd
  exact ⟨F,negative_even_low_ratio_family_leading F hK hp hS hB
    (abs_lt_one_of_primePhaseCosines hprime) hprime⟩

end
end IsingBulk.Joint.FormFactors
