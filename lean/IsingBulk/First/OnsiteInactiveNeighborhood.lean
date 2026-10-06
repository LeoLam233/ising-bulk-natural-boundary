import IsingBulk.First.OnsiteRegularity

/-! A genuine open parameter/angular neighborhood for every inactive source
factor, obtained from the actual denominator values. -/
namespace IsingBulk.First
noncomputable section
open Filter
open scoped Topology ContDiff

/-- The regular rational domain keeps only actual source denominator exclusions. -/
def onsiteInactiveDomain {N : ℕ} (J : Finset (SingularFactorIndex N)) :
    Set ((ℝ × ℂ) × DoubleAngularVector N) :=
  {q | q.1.1 ≠ 0 ∧ q.1.2 ≠ 0 ∧ ∀ f ∈ Jᶜ,
    onsiteFactorDenominator q.1.2 (angleTuple q.1.1 q.2.1) (angleTuple q.1.1 q.2.2) f ≠ 0}

theorem onsiteInactiveDomain_isOpen {N : ℕ} (J : Finset (SingularFactorIndex N)) :
    IsOpen (onsiteInactiveDomain J) := by
  rw [isOpen_iff_mem_nhds]
  rintro ⟨⟨r,s⟩,u⟩ ⟨hr,hs,hden⟩
  have hx (i) : ContDiffAt ℝ ∞
      (fun q : (ℝ × ℂ) × DoubleAngularVector N => angleTuple q.1.1 q.2.1 i) ((r,s),u) :=
    anglePoint_joint_contDiff.contDiffAt.comp ((r,s),u)
      (show ContDiffAt ℝ ∞ (fun q : (ℝ × ℂ) × DoubleAngularVector N =>
        (q.1.1,q.2.1 i)) ((r,s),u) by fun_prop)
  have hy (i) : ContDiffAt ℝ ∞
      (fun q : (ℝ × ℂ) × DoubleAngularVector N => angleTuple q.1.1 q.2.2 i) ((r,s),u) :=
    anglePoint_joint_contDiff.contDiffAt.comp ((r,s),u)
      (show ContDiffAt ℝ ∞ (fun q : (ℝ × ℂ) × DoubleAngularVector N =>
        (q.1.1,q.2.2 i)) ((r,s),u) by fun_prop)
  have hd : ∀ f ∈ Jᶜ, ∀ᶠ q : (ℝ × ℂ) × DoubleAngularVector N in 𝓝 ((r,s),u),
      onsiteFactorDenominator q.1.2 (angleTuple q.1.1 q.2.1) (angleTuple q.1.1 q.2.2) f ≠ 0 := by
    intro f hf
    exact (onsiteFactorDenominator_contDiffAt hx hy contDiffAt_fst.snd
      (fun _ => anglePoint_ne_zero_of_radius hr _) (fun _ => anglePoint_ne_zero_of_radius hr _)
      hs f).continuousAt.eventually_ne (hden f hf)
  have hdall : ∀ᶠ q : (ℝ × ℂ) × DoubleAngularVector N in 𝓝 ((r,s),u), ∀ f ∈ Jᶜ,
      onsiteFactorDenominator q.1.2 (angleTuple q.1.1 q.2.1) (angleTuple q.1.1 q.2.2) f ≠ 0 := by
    exact (Jᶜ).eventually_all.mpr hd
  have hr' : ∀ᶠ q : (ℝ × ℂ) × DoubleAngularVector N in 𝓝 ((r,s),u), q.1.1 ≠ 0 :=
    continuousAt_fst.fst.eventually_ne hr
  have hs' : ∀ᶠ q : (ℝ × ℂ) × DoubleAngularVector N in 𝓝 ((r,s),u), q.1.2 ≠ 0 :=
    continuousAt_fst.snd.eventually_ne hs
  filter_upwards [hr', hs', hdall] with q hqr hqs hqd
  exact ⟨hqr,hqs,hqd⟩

/-- At a unit-torus configuration, selecting all and only active factors places
the original point in the open regular domain for the remaining amplitude. -/
theorem onsite_mem_inactiveDomain {N : ℕ} (s : ℂ) (S : ℝ)
    (hs : s ≠ 0) (hS : sourceS s = (S : ℂ)) (u : DoubleAngularVector N)
    (J : Finset (SingularFactorIndex N))
    (hJ : ∀ f, f ∈ J ↔ isOnsiteFactor f ∧ singularFactorActive (angleTuple 1 u.1) (angleTuple 1 u.2) S f) :
    ((1,s),u) ∈ onsiteInactiveDomain J := by
  refine ⟨one_ne_zero,hs,?_⟩
  intro f hf hz
  have hactive := (onsiteFactorDenominator_zero_iff_active s S _ _
    (fun _ => anglePoint_norm (by norm_num) _) (fun _ => anglePoint_norm (by norm_num) _)
    hS f).mp hz
  exact (Finset.mem_compl.mp hf) ((hJ f).mpr hactive)

end
end IsingBulk.First
