import IsingBulk.Joint.FormFactors.ActualFamilyLeadingTails
import IsingBulk.Joint.Transverse.FamilyPhysicalLeading
import IsingBulk.Anisotropic.Geometry.PrimeOrientation

/-! Uniform first singularities of the actual two-coupling physical bulk
susceptibilities on constructed complex-ratio families. Lambda varies over a
closed complex disk. The common physical side, branch, exact integer particle
weights, complete parity sum and all lower Leibniz terms are proved inputs. -/
namespace IsingBulk.Joint.FormFactors
noncomputable section
open Set Filter Metric IsingBulk.Anisotropic
open scoped Topology

/-- Actual high-temperature complex-ratio family endpoint. The limiting
coefficient is that of the literal normalized complete physical susceptibility,
with one common positive lower bound and one common lambda disk. -/
theorem positive_high_ratio_family_leading {b : ℝ} {z₀ lam₀ : ℂ}
    (F : ComplexRatioFamily (Transverse.positiveParameter (b:ℂ)) highPrefactor 1 z₀ lam₀)
    (hK : (z₀,lam₀*z₀)∈closure highDomain) (hp : p (z₀,lam₀*z₀)^2≠1)
    (hS : S (z₀,lam₀*z₀)≠0) (hB : 0<(transferB (z₀,lam₀*z₀)).im)
    (hb : |b|<1) (hprime : b∈primePhaseCosines) :
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
        M<‖iteratedDeriv k (fun u=>highNormalizedBulk (F.coupling (u,lam))) (Complex.I*(t:ℂ)^2)‖) := by
  obtain ⟨ρ,hρ,hρF,hca,hfront,hSn,hpn,hBn,hn,hside⟩ := F.actual_high_family_inputs hK hp hS hB hb
  obtain ⟨q,k,c,hq,hcritical,hc,hlower,hlimits,hunbounded⟩ :=
    Transverse.positive_high_compact_family_leading F.coupling (isCompact_closedBall _ _) hca hfront hSn hpn hBn hb hprime hn
  exact ⟨ρ,q,k,c,hρ,hρF,hq,hcritical,hc,hside,hlower,hlimits,hunbounded⟩

/-- Actual low-temperature counterpart. Every positive even particle order is
retained, and the zero-particle vacuum remains removed. -/
theorem positive_low_ratio_family_leading {b : ℝ} {z₀ lam₀ : ℂ}
    (F : ComplexRatioFamily (Transverse.positiveParameter (b:ℂ)) lowPrefactor 1 z₀ lam₀)
    (hK : (z₀,lam₀*z₀)∈closure lowDomain) (hp : p (z₀,lam₀*z₀)^2≠1)
    (hS : S (z₀,lam₀*z₀)≠0) (hB : 0<(transferB (z₀,lam₀*z₀)).im)
    (hb : |b|<1) (hprime : b∈primePhaseCosines) :
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
        M<‖iteratedDeriv k (fun u=>lowNormalizedBulk (F.coupling (u,lam))) (Complex.I*(t:ℂ)^2)‖) := by
  obtain ⟨ρ,hρ,hρF,hca,hfront,hSn,hpn,hBn,hn,hside⟩ := F.actual_low_family_inputs hK hp hS hB hb
  obtain ⟨q,k,c,hcritical,hc,hlower,hlimits,hunbounded⟩ :=
    Transverse.positive_low_compact_family_leading F.coupling (isCompact_closedBall _ _) hca hfront hSn hpn hBn hb hprime hn
  exact ⟨ρ,q,k,c,hρ,hρF,hcritical,hc,hside,hlower,hlimits,hunbounded⟩

/-- The actual implicit complex-ratio family and its complete physical
asymptotics are constructed from the original boundary data. -/
theorem exists_positive_high_ratio_family_leading {b : ℝ} {z₀ lam₀ : ℂ}
    (hK : (z₀,lam₀*z₀)∈closure highDomain) (hp : p (z₀,lam₀*z₀)^2≠1)
    (hS : S (z₀,lam₀*z₀)≠0) (hB : 0<(transferB (z₀,lam₀*z₀)).im)
    (hprime : b∈primePhaseCosines)
    (he0 : Transverse.positiveParameter b (z₀,lam₀*z₀)=0)
    (hd : deriv (fun z=>Transverse.positiveParameter b (z,lam₀*z)) z₀≠0) :
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
        M<‖iteratedDeriv k (fun u=>highNormalizedBulk (F.coupling (u,lam))) (Complex.I*(t:ℂ)^2)‖) := by
  obtain ⟨F⟩ := positive_high_complex_ratio_family hK hp hS hB he0 hd
  exact ⟨F,positive_high_ratio_family_leading F hK hp hS hB
    (abs_lt_one_of_primePhaseCosines hprime) hprime⟩

/-- The actual implicit complex-ratio family and its complete physical
asymptotics are constructed from the original boundary data. -/
theorem exists_positive_low_ratio_family_leading {b : ℝ} {z₀ lam₀ : ℂ}
    (hK : (z₀,lam₀*z₀)∈closure lowDomain) (hp : p (z₀,lam₀*z₀)^2≠1)
    (hS : S (z₀,lam₀*z₀)≠0) (hB : 0<(transferB (z₀,lam₀*z₀)).im)
    (hprime : b∈primePhaseCosines)
    (he0 : Transverse.positiveParameter b (z₀,lam₀*z₀)=0)
    (hd : deriv (fun z=>Transverse.positiveParameter b (z,lam₀*z)) z₀≠0) :
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
        M<‖iteratedDeriv k (fun u=>lowNormalizedBulk (F.coupling (u,lam))) (Complex.I*(t:ℂ)^2)‖) := by
  obtain ⟨F⟩ := positive_low_complex_ratio_family hK hp hS hB he0 hd
  exact ⟨F,positive_low_ratio_family_leading F hK hp hS hB
    (abs_lt_one_of_primePhaseCosines hprime) hprime⟩

end
end IsingBulk.Joint.FormFactors
