import IsingBulk.Joint.FormFactors.ActualFamilyLeadingNegativeData
import IsingBulk.Joint.FormFactors.WeightedFamilyTails
import IsingBulk.Joint.RegularEdges.PhysicalIdentity

/-! Genuine mixed tails of the literal physical LT particles on the additive
negative-edge ratio family. The even pi-shift phase is retained through i*S. -/
namespace IsingBulk.Joint.FormFactors
noncomputable section
open Set Filter Metric IsingBulk.Joint.RegularEdges
open scoped Topology
namespace ComplexRatioFamily
variable {b : ℝ} {amp : Coupling→ℂ} {z₀ lam₀ : ℂ}
variable (F : ComplexRatioFamily (Transverse.negativeParameter b) amp (-1) z₀ lam₀)

def actualNegativeFamilyEvenTerm (n : ℕ) (q : Coupling) : ℂ :=
  F.amplitude q*p (F.coupling q)^(n+1)*unscaledFullCoefficient (2*n+2) (F.coupling q)

theorem negative_additive_polydisk_of_ball {q : Coupling} (hq : q∈ball (0,lam₀) F.radius) : q∈F.polydisk := by
  have hh : dist q.1 0<F.radius ∧ dist q.2 lam₀<F.radius := max_lt_iff.mp hq
  exact ⟨hh.1.le,hh.2.le⟩

theorem negative_additive_p_ne_zero {q : Coupling} (hq : q∈F.polydisk) : p (F.coupling q)≠0 := by
  have hs := F.scale_ne_zero hq
  have hb := F.anisotropy_ne_zero hq
  change S (F.coupling q)*T (F.coupling q)≠0
  apply mul_ne_zero hs
  intro hz
  apply hb
  simp only [anisotropy,transferB,hz,zero_div]

/-- Literal complete even contour coefficient equals the correctly phased
independent positive model, on the actual same low-temperature side. -/
theorem negative_additive_fullCoefficient_eq_independent (n : ℕ) {q : Coupling}
    (hq : q∈F.polydisk) (hi : 0<q.1.im) (hK : F.coupling q∈lowDomain) :
    unscaledFullCoefficient (2*n+2) (F.coupling q)=
      independentAngularCoefficient (2*n+1) b (q.1,(-F.anisotropy q,Complex.I*F.scale q)) := by
  rw [show 2*n+2=(2*n+1)+1 by omega,fullCoefficient_eq_physicalAngular_low _ hK]
  exact physicalAngular_eq_negative_even_model (curve:=fun u=>F.coupling (u,q.2))
    ⟨n+1,by omega⟩ (lowDomain_subset_spectralComplement hK) (F.scale_ne_zero hq)
    (F.edge_eq q.1 q.2 (F.polydisk_bounds hq).1 (F.polydisk_bounds hq).2) hi
    (by simpa only [Transverse.negativeCurveB,Complex.neg_im,neg_one_mul,anisotropy,Prod.mk.eta]
      using F.anisotropy_sign hq)

theorem actual_negative_ratio_full_coefficient_mixed_tails (hb : |b|<1) :
    ∃δ : ℝ,0<δ ∧ ∀j : ℕ,∃G : ℕ→ℝ,Summable G ∧ (∀k,0≤G k) ∧
      ∀q∈ball (0,lam₀) δ,0<q.1.im → F.coupling q∈lowDomain → ∀k : ℕ,
        ‖iteratedFDeriv ℂ j (F.actualNegativeFamilyEvenTerm (j+1+k)) q‖≤G k := by
  have h0 : (0,lam₀)∈F.polydisk := F.zero_mem_polydisk (mem_closedBall_self F.radius_pos.le)
  have hFa : AnalyticAt ℂ F.coupling (0,lam₀) := F.negative_additive_ratio_center_analytic
    (mem_closedBall_self F.radius_pos.le)
  have hPa : AnalyticAt ℂ (fun q=>p (F.coupling q)) (0,lam₀) :=
    ((Complex.analyticAt_sinh.comp analyticAt_fst).mul
      (Complex.analyticAt_sinh.comp analyticAt_snd)).comp hFa
  obtain ⟨r,hr,hjets⟩ := local_weighted_coefficient_tails hb (show ((0:ℂ),lam₀).1=0 from rfl)
    (F.anisotropy_analyticOnNhd _ h0).neg
    (analyticAt_const.mul (F.scale_analyticOnNhd _ h0)) hPa
    (F.amplitude_analyticOnNhd _ h0)
    (by simpa only [Pi.neg_apply,Complex.neg_im,neg_one_mul] using F.anisotropy_sign h0)
    (mul_ne_zero Complex.I_ne_zero (F.scale_ne_zero h0)) (F.negative_additive_p_ne_zero h0)
  let δ := min r F.radius
  refine ⟨δ,lt_min hr F.radius_pos,?_⟩
  intro j
  obtain ⟨G,H,_hG,hH,_hG0,hH0,hbnd⟩ := hjets j
  refine ⟨H,hH,hH0,?_⟩
  intro q hq hi hK k
  have hqr : q∈ball (0,lam₀) r := ball_subset_ball (min_le_left _ _) hq
  have hqF : q∈ball (0,lam₀) F.radius := ball_subset_ball (min_le_right _ _) hq
  have hp := F.negative_additive_polydisk_of_ball hqF
  have hfc : ContinuousAt F.coupling q :=
    (F.coupling_analytic q.1 q.2 (F.polydisk_bounds hp).1 (F.polydisk_bounds hp).2).continuousAt
  have heball : ∀ᶠt in 𝓝 q,t∈ball (0,lam₀) F.radius := isOpen_ball.mem_nhds hqF
  have he : ∀ᶠt in 𝓝 q,t∈ball (0,lam₀) F.radius ∧ 0<t.1.im ∧ F.coupling t∈lowDomain :=
    heball.and
      ((continuousAt_const.eventually_lt (Complex.continuous_im.comp continuous_fst).continuousAt hi).and
        (hfc.preimage_mem_nhds (lowDomain_isOpen.mem_nhds hK)))
  have hv : F.actualNegativeFamilyEvenTerm (j+1+k) =ᶠ[𝓝 q]
      familyEvenTerm b (fun q=> -F.anisotropy q) (fun q=>Complex.I*F.scale q)
        (fun t=>p (F.coupling t)) F.amplitude (j+1+k) := by
    filter_upwards [he] with t ht
    unfold actualNegativeFamilyEvenTerm familyEvenTerm
    rw [F.negative_additive_fullCoefficient_eq_independent _ (F.negative_additive_polydisk_of_ball ht.1) ht.2.1 ht.2.2]
  rw [(hv.iteratedFDeriv ℂ j).eq_of_nhds]
  exact (hbnd q hqr hi k).2

/-- The actual side premise is discharged on one closed complex-lambda disk,
chosen before every mixed derivative order. -/
theorem actual_negative_low_ratio_mixed_tails
    (hK : (z₀,lam₀*z₀)∈closure lowDomain) (hp : p (z₀,lam₀*z₀)^2≠1)
    (hS : S (z₀,lam₀*z₀)≠0) (hB : (transferB (z₀,lam₀*z₀)).im<0) (hb : |b|<1) :
    ∃ρ : ℝ,0<ρ ∧ ρ≤F.radius ∧
      (∀lam∈closedBall lam₀ ρ,∀u : ℂ,‖u‖<ρ → 0<u.im → F.coupling (u,lam)∈lowDomain) ∧
      ∀j : ℕ,∃G : ℕ→ℝ,Summable G ∧ (∀k,0≤G k) ∧
        ∀lam∈closedBall lam₀ ρ,∀u : ℂ,‖u‖<ρ → 0<u.im → ∀k : ℕ,
          ‖iteratedFDeriv ℂ j (F.actualNegativeFamilyEvenTerm (j+1+k)) (u,lam)‖≤G k := by
  obtain ⟨r,hr,hrF,hdata,_⟩ := negative_ratio_raw_common_low_side F hK hp hS hB hb
  obtain ⟨δ,hδ,htails⟩ := F.actual_negative_ratio_full_coefficient_mixed_tails hb
  let ρ := min r (δ/2)
  have hρ : 0<ρ := lt_min hr (half_pos hδ)
  have hρr : ρ≤r := min_le_left _ _
  have hρδ : ρ<δ := (min_le_right _ _).trans_lt (half_lt_self hδ)
  have hside (lam : ℂ) (hl : lam∈closedBall lam₀ ρ) (u : ℂ) (hu : ‖u‖<ρ) (hi : 0<u.im) :
      F.coupling (u,lam)∈lowDomain :=
    (hdata u lam (hu.le.trans hρr) ((show ‖lam-lam₀‖≤ρ by simpa only [mem_closedBall,dist_eq_norm] using hl).trans hρr)).2.2.2.2.mpr hi
  refine ⟨ρ,hρ,hρr.trans hrF,hside,?_⟩
  intro j
  obtain ⟨G,hG,hG0,hbound⟩ := htails j
  refine ⟨G,hG,hG0,?_⟩
  intro lam hl u hu hi k
  have hball : (u,lam)∈ball (0,lam₀) δ := by
    rw [mem_ball,Prod.dist_eq,max_lt_iff,dist_zero_right]
    exact ⟨hu.trans hρδ,(show dist lam lam₀≤ρ from hl).trans_lt hρδ⟩
  exact hbound (u,lam) hball hi (hside lam hl u hu hi) k

end ComplexRatioFamily
end
end IsingBulk.Joint.FormFactors
