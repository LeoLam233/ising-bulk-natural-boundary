import IsingBulk.Joint.FormFactors.WeightedFamilyTails
import IsingBulk.Joint.RegularEdges.PhysicalIdentity
import IsingBulk.Joint.RegularEdges.NormalFormIdentity

/-! The compact complex-ratio estimates attached to the literal joint full
contour coefficients, with the actual physical integer weights and prefactor. -/
namespace IsingBulk.Joint.FormFactors
noncomputable section
open Set Filter Metric
open scoped Topology
open IsingBulk.Joint.RegularEdges

namespace ComplexRatioFamily

variable {b : ℝ} {amp : Coupling → ℂ} {z₀ lam₀ : ℂ}
variable (F : ComplexRatioFamily (Transverse.positiveParameter b) amp 1 z₀ lam₀)

theorem family_polydisk_of_ball {q : Coupling} (hq : q∈ball (0,lam₀) F.radius) : q∈F.polydisk := by
  have hh : dist q.1 0<F.radius ∧ dist q.2 lam₀<F.radius := max_lt_iff.mp hq
  exact ⟨hh.1.le,hh.2.le⟩

theorem family_p_ne_zero {q : Coupling} (hq : q∈F.polydisk) : p (F.coupling q)≠0 := by
  have hs := F.scale_ne_zero hq
  have hb := F.anisotropy_ne_zero hq
  change S (F.coupling q)*T (F.coupling q)≠0
  apply mul_ne_zero hs
  intro hz
  apply hb
  simp only [ComplexRatioFamily.anisotropy,transferB,hz,zero_div]

theorem family_fullCoefficient_eq_independent (n : ℕ) {q : Coupling}
    (hq : q∈F.polydisk) (hi : 0<q.1.im) (hK : F.coupling q∈highDomain ∨ F.coupling q∈lowDomain) :
    unscaledFullCoefficient (n+1) (F.coupling q)=
      independentAngularCoefficient n b (q.1,(F.anisotropy q,F.scale q)) := by
  have hs := F.scale_ne_zero hq
  have ho : F.coupling q∉spectralSet := hK.elim (fun h => highDomain_subset_spectralComplement h) (fun h => lowDomain_subset_spectralComplement h)
  have hc : unscaledFullCoefficient (n+1) (F.coupling q)=Negative.unscaledAngularCoefficient n (F.coupling q) := by
    rcases hK with hK|hK
    · exact fullCoefficient_eq_physicalAngular_high n hK hs
    · exact fullCoefficient_eq_physicalAngular_low n hK
  rw [hc]
  have hh := physicalAngular_eq_positiveCoefficient n (curve := fun u => F.coupling (u,q.2)) ho hs
    (F.edge_eq q.1 q.2 (F.polydisk_bounds hq).1 (F.polydisk_bounds hq).2) hi
    (by simpa only [Transverse.curveB,one_mul,ComplexRatioFamily.anisotropy,Prod.mk.eta] using F.anisotropy_sign hq)
  exact hh

/-- A complete actual complex-ratio normalized particle term. The two values
of parity give the literal odd HT and even LT terms, including the onsite part. -/
def actualFamilyOddTerm (n : ℕ) (q : Coupling) : ℂ :=
  F.amplitude q*p (F.coupling q)^n*unscaledFullCoefficient (2*n+1) (F.coupling q)
def actualFamilyEvenTerm (n : ℕ) (q : Coupling) : ℂ :=
  F.amplitude q*p (F.coupling q)^(n+1)*unscaledFullCoefficient (2*n+2) (F.coupling q)

theorem actual_complex_ratio_full_coefficient_mixed_tails (hb : |b|<1) :
    ∃ δ : ℝ, 0<δ ∧ ∀ j : ℕ, ∃ G H : ℕ→ℝ,
      Summable G ∧ Summable H ∧ (∀ k, 0≤G k) ∧ (∀ k, 0≤H k) ∧
      ∀ q∈ball (0,lam₀) δ, 0<q.1.im →
        F.coupling q∈highDomain ∪ lowDomain → ∀ k : ℕ,
      ‖iteratedFDeriv ℂ j (F.actualFamilyOddTerm (j+2+k)) q‖≤G k ∧
      ‖iteratedFDeriv ℂ j (F.actualFamilyEvenTerm (j+1+k)) q‖≤H k := by
  have h0 : (0,lam₀)∈F.polydisk := F.zero_mem_polydisk (mem_closedBall_self F.radius_pos.le)
  have hFa : AnalyticAt ℂ F.coupling (0,lam₀) := F.coupling_analytic 0 lam₀
    (by simp only [norm_zero]; linarith [F.radius_pos])
    (by simp only [sub_self,norm_zero]; linarith [F.radius_pos])
  have hPa : AnalyticAt ℂ (fun q => p (F.coupling q)) (0,lam₀) :=
    ((Complex.analyticAt_sinh.comp analyticAt_fst).mul
      (Complex.analyticAt_sinh.comp analyticAt_snd)).comp hFa
  obtain ⟨r,hr,hjets⟩ := local_weighted_coefficient_tails hb (show ((0:ℂ),lam₀).1=0 from rfl)
    (F.anisotropy_analyticOnNhd _ h0) (F.scale_analyticOnNhd _ h0) hPa
    (F.amplitude_analyticOnNhd _ h0) (by simpa only [one_mul] using F.anisotropy_sign h0)
    (F.scale_ne_zero h0) (F.family_p_ne_zero h0)
  let δ := min r F.radius
  refine ⟨δ,lt_min hr F.radius_pos,?_⟩
  intro j
  obtain ⟨G,H,hG,hH,hG0,hH0,hbnd⟩ := hjets j
  refine ⟨G,H,hG,hH,hG0,hH0,?_⟩
  intro q hq hi hK k
  have hqr : q∈ball (0,lam₀) r := ball_subset_ball (min_le_left _ _) hq
  have hqF : q∈ball (0,lam₀) F.radius := ball_subset_ball (min_le_right _ _) hq
  have hp := F.family_polydisk_of_ball hqF
  have hfc : ContinuousAt F.coupling q :=
    (F.coupling_analytic q.1 q.2 (F.polydisk_bounds hp).1 (F.polydisk_bounds hp).2).continuousAt
  have heball : ∀ᶠ t in 𝓝 q, t∈ball (0,lam₀) F.radius := isOpen_ball.mem_nhds hqF
  have he : ∀ᶠ t in 𝓝 q, t∈ball (0,lam₀) F.radius ∧ 0<t.1.im ∧ F.coupling t∈highDomain∪lowDomain :=
    heball.and
      ((continuousAt_const.eventually_lt (Complex.continuous_im.comp continuous_fst).continuousAt hi).and
        (hfc.preimage_mem_nhds ((highDomain_isOpen.union lowDomain_isOpen).mem_nhds hK)))
  have ho : F.actualFamilyOddTerm (j+2+k) =ᶠ[𝓝 q]
      familyOddTerm b F.anisotropy F.scale (fun t => p (F.coupling t)) F.amplitude (j+2+k) := by
    filter_upwards [he] with t ht
    unfold actualFamilyOddTerm familyOddTerm
    rw [F.family_fullCoefficient_eq_independent _ (F.family_polydisk_of_ball ht.1) ht.2.1 ht.2.2]
  have hv : F.actualFamilyEvenTerm (j+1+k) =ᶠ[𝓝 q]
      familyEvenTerm b F.anisotropy F.scale (fun t => p (F.coupling t)) F.amplitude (j+1+k) := by
    filter_upwards [he] with t ht
    unfold actualFamilyEvenTerm familyEvenTerm
    rw [show 2*(j+1+k)+2=(2*(j+1+k)+1)+1 by omega,
      F.family_fullCoefficient_eq_independent _ (F.family_polydisk_of_ball ht.1) ht.2.1 ht.2.2]
  rw [(ho.iteratedFDeriv ℂ j).eq_of_nhds,(hv.iteratedFDeriv ℂ j).eq_of_nhds]
  exact hbnd q hqr hi k

end ComplexRatioFamily
end
end IsingBulk.Joint.FormFactors
