import IsingBulk.Joint.FormFactors.ActualFamilyLeadingNegative
import IsingBulk.Joint.FormFactors.ActualFamilyLeadingNegativeTails

/-! The actual negative-even LT complete leading limit and every mixed
particle tail hold on the same genuine complex-ratio parameter polydisk. -/
namespace IsingBulk.Joint.FormFactors
noncomputable section
open Set Filter Metric IsingBulk.Anisotropic
open scoped Topology

theorem negative_even_low_ratio_family_leading_and_mixed_tails {b : ℝ} {z₀ lam₀ : ℂ}
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
        M<‖iteratedDeriv k (fun u=>lowNormalizedBulk (F.coupling (u,lam))) (Complex.I*(t:ℂ)^2)‖) ∧
      (∀j : ℕ,∃G : ℕ→ℝ,Summable G ∧ (∀m,0≤G m) ∧
        ∀lam∈closedBall lam₀ ρ,∀u : ℂ,‖u‖<ρ → 0<u.im → ∀m : ℕ,
          ‖iteratedFDeriv ℂ j (F.actualNegativeFamilyEvenTerm (j+1+m)) (u,lam)‖≤G m) := by
  obtain ⟨r,q,k,c,hr,hrF,hcritical,hc,hside,hlower,hlimits,hunbounded⟩ :=
    negative_even_low_ratio_family_leading F hK hp hS hB hb hprime
  obtain ⟨s,hs,_hsF,_hsideS,htails⟩ := F.actual_negative_low_ratio_mixed_tails hK hp hS hB hb
  let ρ := min r s
  have hρ : 0<ρ := lt_min hr hs
  have hρr : ρ≤r := min_le_left _ _
  have hρs : ρ≤s := min_le_right _ _
  have hsubr : closedBall lam₀ ρ⊆closedBall lam₀ r := closedBall_subset_closedBall hρr
  have hsubs : closedBall lam₀ ρ⊆closedBall lam₀ s := closedBall_subset_closedBall hρs
  refine ⟨ρ,q,k,c,hρ,hρr.trans hrF,hcritical,hc,?_,?_,?_,?_,?_⟩
  · intro lam hl u hu
    exact hside lam (hsubr hl) u (hu.trans hρr)
  · intro lam hl
    exact hlower lam (hsubr hl)
  · intro j hj
    exact (hlimits j hj).mono hsubr
  · intro M
    filter_upwards [hunbounded M] with t ht
    exact fun lam hl=>ht lam (hsubr hl)
  · intro j
    obtain ⟨G,hG,hG0,hbound⟩ := htails j
    exact ⟨G,hG,hG0,fun lam hl u hu hi m=>hbound lam (hsubs hl) u (hu.trans_le hρs) hi m⟩

/-- Construction and all quantitative family conclusions on one common disk. -/
theorem exists_negative_even_low_ratio_family_leading_and_mixed_tails {b : ℝ} {z₀ lam₀ : ℂ}
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
        M<‖iteratedDeriv k (fun u=>lowNormalizedBulk (F.coupling (u,lam))) (Complex.I*(t:ℂ)^2)‖) ∧
      (∀j : ℕ,∃G : ℕ→ℝ,Summable G ∧ (∀m,0≤G m) ∧
        ∀lam∈closedBall lam₀ ρ,∀u : ℂ,‖u‖<ρ → 0<u.im → ∀m : ℕ,
          ‖iteratedFDeriv ℂ j (F.actualNegativeFamilyEvenTerm (j+1+m)) (u,lam)‖≤G m) := by
  obtain ⟨F⟩ := negative_even_low_complex_ratio_family hK hp hS hB he0 hd
  exact ⟨F,negative_even_low_ratio_family_leading_and_mixed_tails F hK hp hS hB
    (abs_lt_one_of_primePhaseCosines hprime) hprime⟩

end
end IsingBulk.Joint.FormFactors
