import IsingBulk.Tail.MixedActiveRestriction
import IsingBulk.Tail.MixedSectorDomain

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter
open scoped Topology

theorem sector_negative_lowerChord_small {b θ inner η : ℝ}
    (hb : 0<Real.sin b) (hη : 0<η) (hi : 0≤ inner)
    (hsmall : inner≤η*Real.sin b/4) (hsin : Real.sin θ<0)
    (hprofile : |sectorDisplacement b θ|≤ inner) : lowerChord b θ<η^2 := by
  have hu : |Real.cos θ-Real.cos b|≤ inner := by
    simpa only [sectorDisplacement,abs_sub_comm] using hprofile
  have hsum : |Real.cos θ+Real.cos b|≤2 :=
    (abs_add_le _ _).trans (by linarith [Real.abs_cos_le_one θ,Real.abs_cos_le_one b])
  have he : (Real.sin θ+Real.sin b)*(Real.sin b-Real.sin θ)=
      (Real.cos θ-Real.cos b)*(Real.cos θ+Real.cos b) := by
    nlinarith [Real.sin_sq_add_cos_sq θ,Real.sin_sq_add_cos_sq b]
  have heabs := congrArg abs he
  rw [abs_mul,abs_mul,abs_of_pos (show 0<Real.sin b-Real.sin θ by linarith)] at heabs
  have hvprod : |Real.sin θ+Real.sin b| *Real.sin b≤2*inner := by
    calc
      _ ≤ |Real.sin θ+Real.sin b| *(Real.sin b-Real.sin θ) :=
        mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      _ = |Real.cos θ-Real.cos b| * |Real.cos θ+Real.cos b| := heabs
      _ ≤ inner*2 := mul_le_mul hu hsum (abs_nonneg _) hi
      _ = _ := by ring
  have hv : |Real.sin θ+Real.sin b|≤η/2 := by nlinarith
  have hui : inner≤η/4 := by nlinarith [Real.sin_le_one b]
  have hu' : |Real.cos θ-Real.cos b|≤η/4 := hu.trans hui
  have hu2 := sq_abs (Real.cos θ-Real.cos b)
  have hv2 := sq_abs (Real.sin θ+Real.sin b)
  unfold lowerChord
  nlinarith [abs_nonneg (Real.cos θ-Real.cos b),abs_nonneg (Real.sin θ+Real.sin b)]

/-- The entire active current slice lies on proved selector plateaus.
The named current coordinate is retained as the compact anchor. -/
theorem mixed_current_active_plateaus {N : ℕ} (b η α inner : ℝ)
    (hb : 0<Real.sin b) (hη : 0<η) (hηsmall : η≤Real.sin b/4)
    (hα : 0<α) (hαsmall : α<Real.sin b/4) (hi : 0≤ inner)
    (his : inner≤(Real.sin b)^2/4) (hip : inner≤η*Real.sin b/4)
    (J : Finset (Fin N)) (q : Fin N) (θ : Fin N → ℝ)
    (hprofile : ∀ i∈J,|sectorDisplacement b (θ i)|≤ inner)
    (hSource : θ∈tsupport (namedSelectorDerivative (constructedSelector b η α) q)) :
    (∀ i∈J,Real.sin (θ i)<0) ∧
    (∀ i∈insert q J,(constructedSelector b η α).p =ᶠ[𝓝 (θ i)]
      (fun _ => (constructedSelector b η α).p (θ i))) ∧
    (∀ i∈insert q J,(constructedSelector b η α).m =ᶠ[𝓝 (θ i)]
      (fun _ => (constructedSelector b η α).m (θ i))) := by
  have hsin (i : Fin N) (hiJ : i∈J) : Real.sin (θ i)<0 :=
    mixed_source_branch_sine_negative b η α inner hb hα hαsmall hi his θ i q (hprofile i hiJ) (Or.inr hSource)
  have hp (i : Fin N) (hiS : i∈insert q J) :
      (constructedSelector b η α).p =ᶠ[𝓝 (θ i)] (fun _ => (constructedSelector b η α).p (θ i)) ∧
      (constructedSelector b η α).m =ᶠ[𝓝 (θ i)] (fun _ => (constructedSelector b η α).m (θ i)) := by
    rcases Finset.mem_insert.mp hiS with heq | hiJ
    · subst i
      obtain ⟨hp,hm⟩ := constructed_current_named_plateau_germ b η α hb hη hηsmall hα q hSource
      exact ⟨hp.trans (Eventually.of_forall (fun _ => hp.eq_of_nhds.symm)),
        hm.trans (Eventually.of_forall (fun _ => hm.eq_of_nhds.symm))⟩
    · have hc := sector_negative_lowerChord_small hb hη hi hip (hsin i hiJ) (hprofile i hiJ)
      obtain ⟨hp,hm⟩ := constructed_branch_plateau_germ hb hη hηsmall hα hc
      exact ⟨hp.trans (Eventually.of_forall (fun _ => hp.eq_of_nhds.symm)),
        hm.trans (Eventually.of_forall (fun _ => hm.eq_of_nhds.symm))⟩
  exact ⟨hsin,fun i hiS => (hp i hiS).1,fun i hiS => (hp i hiS).2⟩

end
end IsingBulk.Tail
