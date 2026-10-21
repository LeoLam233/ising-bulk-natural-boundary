import IsingBulk.HT.Contour.SignedKernel
import IsingBulk.Tail.CurrentGlobalEnvelope

/-! The protected disk is unchanged by either HT sign. These are actual
constructed-contour bounds, including complex parameter variation and
arbitrary occupancy. Constants are chosen before N and before the sign. -/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.Branch Set
open scoped Topology

theorem signed_exponential_attenuation_linear_gap {a lam : ℝ} {σ Z : ℂ}
    (hσ : ‖σ‖ = 1) (ha : 0 ≤ a) (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hZ : ‖Z‖ ≤ Real.exp (-a*lam)) :
    a*Real.exp (-a)*lam ≤ ‖1-σ*Z‖ := by
  apply exponential_attenuation_linear_gap ha hlam hlam1
  simpa only [norm_mul,hσ,one_mul] using hZ

/-- The exact lambda-squared denominator cost, including the negative sign. -/
theorem signed_current_global_denominator_lower {a b lam : ℝ} {σ Z Y : ℂ}
    (hσ : ‖σ‖ = 1) (ha : 0<a) (hb : 0<b) (hlam : 0≤lam) (hlam1 : lam≤1)
    (hZ : ‖Z‖ ≤ Real.exp (-a*lam)) (hY : ‖Y‖ ≤ Real.exp (-b*lam)) :
    (a*b*Real.exp (-(a+b)))*lam^2 ≤ ‖(1-σ*Z)*(1-σ*Y)‖ := by
  exact current_global_denominator_lower ha hb hlam hlam1
    (by simpa only [norm_mul,hσ,one_mul] using hZ)
    (by simpa only [norm_mul,hσ,one_mul] using hY)

/-- Protected complex disks and both signed global gaps for the literal
constructed named current. There is no assumed contour certificate. -/
theorem signed_constructed_current_actual_root_disk (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ η₀ τ₀ : ℝ, 0 < η₀ ∧ 0 < τ₀ ∧
      ∀ η α τ : ℝ, 0 < η → η < η₀ → 0 < α → α < Real.sin d.thetaB/4 →
        0 < τ → τ < τ₀ → ∃ c eps₀ gZ gY : ℝ,
        0 < c ∧ 0 < eps₀ ∧ 0 < gZ ∧ 0 < gY ∧
        ∀ (N : ℕ) (eps lamStar lam : ℝ) (θ : Fin N → ℝ) (q : Fin N) (s σ : ℂ),
          1 ≤ N → 0 < eps → eps < eps₀ → 0 < lamStar → lamStar ≤ lam → lam ≤ 1 →
          θ ∈ angleBox N →
          θ ∈ tsupport (namedSelectorDerivative (constructedSelector d.thetaB η α) q) →
          ‖s-radialParameter d.theta eps‖ ≤ c*lamStar/(N:ℝ)^2 → ‖σ‖=1 →
          s ≠ 0 ∧
          (∀ i, sourceW s (deformedPoint (constructedSelector d.thetaB η α)
            (Real.exp (-d.c₀*eps)) τ lam θ i) ∈ continuedRootDomain) ∧
          gZ*lam ≤ ‖1-σ*coordinateProduct (fun i => selectedContinuedRoot s
            (deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ lam θ i))‖ ∧
          gY*lam ≤ ‖1-σ*coordinateProduct (deformedPoint (constructedSelector d.thetaB η α)
            (Real.exp (-d.c₀*eps)) τ lam θ)‖ := by
  obtain ⟨η₀,τ₀,hη₀,hτ₀,hmain⟩ := constructed_current_actual_root_disk d hcsmall
  refine ⟨η₀,τ₀,hη₀,hτ₀,?_⟩
  intro η α τ hη hηlt hα hαsmall hτ hτlt
  obtain ⟨c,e,a,hc,he,ha,hroot⟩ := hmain η α τ hη hηlt hα hαsmall hτ hτlt
  refine ⟨c,e,a*Real.exp (-a),(3*τ/2)*Real.exp (-(3*τ/2)),hc,he,
    by positivity,by positivity,?_⟩
  intro N eps lamStar lam θ q s σ hN heps hepslt hls hl hl1 hθ hsupp hsd hσ
  obtain ⟨hs,hW,hZ,hY⟩ := hroot N eps lamStar lam θ q s hN heps hepslt hls hl hl1 hθ hsupp hsd
  exact ⟨hs,hW,
    signed_exponential_attenuation_linear_gap hσ ha.le (hls.le.trans hl) hl1 hZ,
    signed_exponential_attenuation_linear_gap hσ (by positivity) (hls.le.trans hl) hl1 hY⟩

end
end IsingBulk.HT.Contour
