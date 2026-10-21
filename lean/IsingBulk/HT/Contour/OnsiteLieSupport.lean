import IsingBulk.HT.Contour.OnsiteLieSmooth
import IsingBulk.Tail.MixedSourcePlateaus

/-! The actual original and named-current weights have a common onsite
smooth-domain cover on every positive particle number, on the full real
homotopy interval after its fixed small strength is chosen. -/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail IsingBulk.HT.Lie Set Filter Metric
open scoped Topology ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def onsiteOriginalSectorWeight {N : ℕ} (f : SelectorFunctions) (b inner : ℝ)
    (hi : 0< inner) (sigma : Fin N → Fin 3) (θ : Fin N → ℝ) : ℂ :=
  (angularSelector f θ*sectorAssignmentWeight b inner hi sigma θ : ℝ)

def onsiteNamedSectorWeight {N : ℕ} (f : SelectorFunctions) (b inner : ℝ)
    (hi : 0< inner) (q : Fin N) (sigma : Fin N → Fin 3) (τ : ℝ) (θ : Fin N → ℝ) : ℂ :=
  -2*Complex.I*(τ:ℂ)*(namedSelectorDerivative f q θ*sectorAssignmentWeight b inner hi sigma θ : ℝ)

theorem onsiteOriginalSectorWeight_smooth {N : ℕ} (f : SelectorFunctions) (hf : RegularSelector f)
    (b inner : ℝ) (hi : 0< inner) (sigma : Fin N → Fin 3) :
    ContDiff ℝ ∞ (onsiteOriginalSectorWeight f b inner hi sigma) :=
  Complex.ofRealCLM.contDiff.comp ((angularSelector_contDiff f hf).mul
    (sector_assignment_smooth b inner hi sigma))

theorem onsiteNamedSectorWeight_smooth {N : ℕ} (f : SelectorFunctions) (hf : RegularSelector f)
    (b inner : ℝ) (hi : 0< inner) (q : Fin N) (sigma : Fin N → Fin 3) (τ : ℝ) :
    ContDiff ℝ ∞ (onsiteNamedSectorWeight f b inner hi q sigma τ) :=
  contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
    ((namedSelectorDerivative_smooth f hf q).mul (sector_assignment_smooth b inner hi sigma)))

theorem onsiteOriginalSectorWeight_periodic {N : ℕ} (f : SelectorFunctions) (hf : RegularSelector f)
    (b inner : ℝ) (hi : 0< inner) (sigma : Fin N → Fin 3) :
    CoordinatePeriodic N (onsiteOriginalSectorWeight f b inner hi sigma) := by
  intro θ q
  unfold onsiteOriginalSectorWeight
  rw [angularSelector_periodic f hf,sectorAssignmentWeight_periodic]

theorem onsiteNamedSectorWeight_periodic {N : ℕ} (f : SelectorFunctions) (hf : RegularSelector f)
    (b inner : ℝ) (hi : 0< inner) (q : Fin N) (sigma : Fin N → Fin 3) (τ : ℝ) :
    CoordinatePeriodic N (onsiteNamedSectorWeight f b inner hi q sigma τ) := by
  intro θ i
  unfold onsiteNamedSectorWeight
  rw [namedSelectorDerivative_periodic f hf,sectorAssignmentWeight_periodic]

theorem onsiteOriginalSectorWeight_support {N : ℕ} (f : SelectorFunctions)
    (b inner : ℝ) (hi : 0< inner) (sigma : Fin N → Fin 3) :
    tsupport (onsiteOriginalSectorWeight f b inner hi sigma) ⊆
      tsupport (fun θ => angularSelector f θ*sectorAssignmentWeight b inner hi sigma θ) :=
  tsupport_comp_subset (g := Complex.ofReal) (by simp) _

theorem onsiteNamedSectorWeight_support {N : ℕ} (f : SelectorFunctions)
    (b inner : ℝ) (hi : 0< inner) (q : Fin N) (sigma : Fin N → Fin 3) (τ : ℝ) :
    tsupport (onsiteNamedSectorWeight f b inner hi q sigma τ) ⊆
      tsupport (fun θ => namedSelectorDerivative f q θ*sectorAssignmentWeight b inner hi sigma θ) :=
  tsupport_mul_subset_right.trans (tsupport_comp_subset (g := Complex.ofReal) (by simp) _)

theorem onsite_real_weight_tsupport_eq {N : ℕ} (w : (Fin N → ℝ) → ℝ) :
    tsupport (fun θ => (w θ:ℂ))=tsupport w := by
  unfold tsupport
  congr 1
  ext θ
  simp only [Function.mem_support,ne_eq,Complex.ofReal_eq_zero]

theorem onsiteOriginalSectorWeight_tsupport_eq {N : ℕ} (f : SelectorFunctions)
    (b inner : ℝ) (hi : 0< inner) (sigma : Fin N → Fin 3) :
    tsupport (onsiteOriginalSectorWeight f b inner hi sigma)=
      tsupport (fun θ => angularSelector f θ*sectorAssignmentWeight b inner hi sigma θ) := by
  unfold tsupport
  congr 1
  ext θ
  simp only [Function.mem_support,onsiteOriginalSectorWeight,ne_eq,Complex.ofReal_eq_zero]

theorem onsiteNamedSectorWeight_tsupport_eq {N : ℕ} (f : SelectorFunctions)
    (b inner : ℝ) (hi : 0< inner) (q : Fin N) (sigma : Fin N → Fin 3)
    {τ : ℝ} (hτ : τ≠0) :
    tsupport (onsiteNamedSectorWeight f b inner hi q sigma τ)=
      tsupport (fun θ => namedSelectorDerivative f q θ*sectorAssignmentWeight b inner hi sigma θ) := by
  have hc : -2*Complex.I*(τ:ℂ)≠0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) (by exact_mod_cast hτ)
  unfold tsupport
  congr 1
  ext θ
  change (-2*Complex.I*(τ:ℂ)*(namedSelectorDerivative f q θ*
    sectorAssignmentWeight b inner hi sigma θ:ℝ)≠0) ↔ _
  rw [mul_ne_zero_iff_left hc]
  simp only [ne_eq,Complex.ofReal_eq_zero,Function.mem_support]

/-- Actual supports put every branch field coordinate strictly inside the
true lower selector plateau, so every restricted occupancy jet vanishes. -/
theorem onsite_sector_support_plateaus {N : ℕ} {b η α inner : ℝ}
    (hb : 0<Real.sin b) (hη : 0<η) (hηsmall : η≤Real.sin b/4)
    (hα : 0<α) (hαsmall : α<Real.sin b/4) (hi : 0< inner)
    (his : inner≤(Real.sin b)^2/4) (hip : inner≤η*Real.sin b/4)
    (q : Fin N) (sigma : Fin N → Fin 3) (τ : ℝ) (θ : Fin N → ℝ)
    (hsupp : θ∈tsupport (onsiteOriginalSectorWeight (constructedSelector b η α) b inner hi sigma) ∨
      θ∈tsupport (onsiteNamedSectorWeight (constructedSelector b η α) b inner hi q sigma τ)) :
    ∀ i∈mixedBranchIndexSet sigma, lowerChord b (θ i)<η^2 ∧
      (constructedSelector b η α).p =ᶠ[𝓝 (θ i)] (fun _ => 0) ∧
      (constructedSelector b η α).m =ᶠ[𝓝 (θ i)] (fun _ => 1) := by
  have hdata : (θ∈tsupport (angularSelector (constructedSelector b η α)) ∨
      θ∈tsupport (namedSelectorDerivative (constructedSelector b η α) q)) ∧
      θ∈tsupport (sectorAssignmentWeight b inner hi sigma) := by
    rcases hsupp with hK | hS
    · have hh := onsiteOriginalSectorWeight_support _ b inner hi sigma hK
      exact ⟨Or.inl (tsupport_mul_subset_left hh),tsupport_mul_subset_right hh⟩
    · have hh := onsiteNamedSectorWeight_support _ b inner hi q sigma τ hS
      exact ⟨Or.inr (tsupport_mul_subset_left hh),tsupport_mul_subset_right hh⟩
  intro i hiJ
  have hσ : sigma i=2 := by simpa [mixedBranchIndexSet] using hiJ
  have hh := sector_assignment_tsupport b inner hi sigma hdata.2 i
  rw [hσ] at hh
  have hprofile := sector_branch_label_profile hi hh
  have hsin := mixed_source_branch_sine_negative b η α inner hb hα hαsmall
    hi.le his θ i q hprofile hdata.1
  have hcore := sector_negative_lowerChord_small hb hη hi.le hip hsin hprofile
  exact ⟨hcore,constructed_branch_plateau_germ hb hη hηsmall hα hcore⟩

/-- No difference separation is needed, even when J is empty or contains
all indices. Every source-coordinate upper-sheet margin is proved from the
actual coupled contour geometry. -/
theorem onsite_actual_domain_cover (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) :
    ∃ c e t₀ : ℝ,0<c ∧ c≤1/4 ∧ 0<e ∧ 0<t₀ ∧
      ∀ η α inner : ℝ,0<η → η≤Real.sin d.thetaB/4 → 0<α → α<Real.sin d.thetaB/4 →
      0≤ inner → inner≤(Real.sin d.thetaB)^2/4 →
      ∀ (N : ℕ) (eps τ lam : ℝ) (θ : Fin N → ℝ) (J : Finset (Fin N)) (q : Fin N) (s : ℂ),
      1≤N → 0<eps → eps<e → 0≤τ → 0≤lam → lam≤1 → lam*τ<t₀ →
      (∀ i∈J,|sectorDisplacement d.thetaB (θ i)|≤ inner) →
      (θ∈tsupport (angularSelector (constructedSelector d.thetaB η α)) ∨
        θ∈tsupport (namedSelectorDerivative (constructedSelector d.thetaB η α) q)) →
      ‖s-radialParameter d.theta eps‖≤c*eps →
      (s,θ)∈onsiteLieDomain J (constructedSelector d.thetaB η α)
        (Real.exp (-d.c₀*eps)) τ lam := by
  obtain ⟨cG,e,t₀,hcG,he,ht,hGeometry⟩ := mixed_actual_uniform_source_data d hcsmall 1 zero_lt_one
  refine ⟨min cG (1/4),e,t₀,lt_min hcG (by norm_num),min_le_right _ _,he,ht,?_⟩
  intro η α inner hη hηsmall hα hαsmall hi his N eps τ lam θ J q s hN heps hepslt hτ hl0 hl1 htl hBP hSource hs
  let f := constructedSelector d.thetaB η α
  let r := Real.exp (-d.c₀*eps)
  have hr : 0<r := Real.exp_pos _
  have hs0 : s≠0 := by
    intro heq
    have hh := hs.trans (mul_le_mul_of_nonneg_right (min_le_right cG (1/4)) heps.le)
    rw [heq,zero_sub,norm_neg,radialParameter_norm heps.le] at hh
    linarith
  obtain ⟨_,hcoords⟩ := hGeometry η α hη hηsmall hα N eps τ lam θ s hN heps hepslt hτ hl0 hl1 htl
    (hs.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) heps.le))
  refine ⟨hs0,?_,?_⟩
  · intro i
    obtain ⟨_,_,_,_,hh⟩ := hcoords i
    exact hh
  · intro i hiJ
    have hsin := mixed_source_branch_sine_negative d.thetaB η α inner d.a_pos hα hαsmall
      hi his θ i q (hBP i hiJ) hSource
    exact lower_halfplane_inverse_difference_ne_zero (mixed_actual_deformed_lower f hr τ lam θ i hsin)

/-- The weights appearing in onsite K and each named current have this
source domain on the whole support, not merely the integration cube. -/
theorem onsite_sector_support_covers (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) :
    ∃ c e t₀ : ℝ,0<c ∧ c≤1/4 ∧ 0<e ∧ 0<t₀ ∧
      ∀ η α inner : ℝ,0<η → η≤Real.sin d.thetaB/4 → 0<α → α<Real.sin d.thetaB/4 →
      ∀ hi : 0< inner,inner≤(Real.sin d.thetaB)^2/4 →
      ∀ (n : ℕ) (eps τ lam : ℝ) (q : Fin (n+1)) (sigma : Fin (n+1) → Fin 3),
      0<eps → eps<e → 0≤τ → 0≤lam → lam≤1 → lam*τ<t₀ →
      let f := constructedSelector d.thetaB η α
      let r := Real.exp (-d.c₀*eps)
      let U := ball (radialParameter d.theta eps) (c*eps)
      U ×ˢ tsupport (onsiteOriginalSectorWeight f d.thetaB inner hi sigma) ⊆
        onsiteLieDomain (mixedBranchIndexSet sigma) f r τ lam ∧
      U ×ˢ tsupport (onsiteNamedSectorWeight f d.thetaB inner hi q sigma τ) ⊆
        onsiteLieDomain (mixedBranchIndexSet sigma) f r τ lam := by
  obtain ⟨c,e,t₀,hc,hcsmall',he,ht,hcover⟩ := onsite_actual_domain_cover d hcsmall
  refine ⟨c,e,t₀,hc,hcsmall',he,ht,?_⟩
  intro η α inner hη hηsmall hα hαsmall hi his n eps τ lam q sigma heps hepslt hτ hl0 hl1 htl
  let f := constructedSelector d.thetaB η α
  have hprofile (θ : Fin (n+1) → ℝ)
      (hassign : θ∈tsupport (sectorAssignmentWeight d.thetaB inner hi sigma))
      (i : Fin (n+1)) (hiJ : i∈mixedBranchIndexSet sigma) :
      |sectorDisplacement d.thetaB (θ i)|≤ inner := by
    have hσ : sigma i=2 := by simpa [mixedBranchIndexSet] using hiJ
    have hh := sector_assignment_tsupport d.thetaB inner hi sigma hassign i
    rw [hσ] at hh
    exact sector_branch_label_profile hi hh
  constructor
  · rintro p ⟨hpU,hpw⟩
    have hsupp := onsiteOriginalSectorWeight_support f d.thetaB inner hi sigma hpw
    exact hcover η α inner hη hηsmall hα hαsmall hi.le his (n+1) eps τ lam p.2
      (mixedBranchIndexSet sigma) q p.1 (by omega) heps hepslt hτ hl0 hl1 htl
      (hprofile p.2 (tsupport_mul_subset_right hsupp)) (Or.inl (tsupport_mul_subset_left hsupp))
      (show ‖p.1-radialParameter d.theta eps‖≤c*eps from
        (show ‖p.1-radialParameter d.theta eps‖<c*eps from by
          simpa only [mem_ball,dist_eq_norm] using hpU).le)
  · rintro p ⟨hpU,hpw⟩
    have hsupp := onsiteNamedSectorWeight_support f d.thetaB inner hi q sigma τ hpw
    exact hcover η α inner hη hηsmall hα hαsmall hi.le his (n+1) eps τ lam p.2
      (mixedBranchIndexSet sigma) q p.1 (by omega) heps hepslt hτ hl0 hl1 htl
      (hprofile p.2 (tsupport_mul_subset_right hsupp)) (Or.inr (tsupport_mul_subset_left hsupp))
      (show ‖p.1-radialParameter d.theta eps‖≤c*eps from
        (show ‖p.1-radialParameter d.theta eps‖<c*eps from by
          simpa only [mem_ball,dist_eq_norm] using hpU).le)

end
end IsingBulk.HT.Contour
