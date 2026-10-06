import IsingBulk.Tail.NestedCutoffs
import IsingBulk.Tail.SelectorCutoffs
import IsingBulk.First.PeriodicBump

/-! Actual smooth periodic nested branch cutoffs, with every finite jet
inside an open m=1 plateau. This constructs the source's fixed branch weights. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First Set Filter
open scoped Topology ContDiff

def periodicBranchChi (b δ : ℝ) (hδ : 0 < δ) (θ : ℝ) : ℝ :=
  periodicizeBump (fun _ : Fin 1 => -b)
    (fun x : Fin 1 → ℝ => fixedBranchBump δ hδ (x 0+b)) (fun _ => θ)

theorem periodicBranchChi_formula (b δ : ℝ) (hδ : 0 < δ) (θ : ℝ) :
    periodicBranchChi b δ hδ θ = fixedBranchBump δ hδ (periodicAngle (θ+b)) := by
  simp [periodicBranchChi,periodicizeBump,centeredWrap]

theorem periodicBranchChi_smooth (b δ : ℝ) (hδ : 0 < δ) (hsmall : δ ≤ 1/2) :
    ContDiff ℝ ∞ (periodicBranchChi b δ hδ) := by
  have hw : ContDiff ℝ ∞ (fun x : Fin 1 → ℝ => fixedBranchBump δ hδ (x 0+b)) :=
    (fixedBranchBump δ hδ).contDiff.comp (by fun_prop)
  have hs : ∀ x : Fin 1 → ℝ, fixedBranchBump δ hδ (x 0+b) ≠ 0 →
      ∀ i : Fin 1, |x i-(-b)| ≤ 1/2 := by
    intro x hx i
    have hi : i=0 := Subsingleton.elim _ _
    subst i
    simpa only [sub_neg_eq_add] using (fixedBranchBump_support δ hδ hx).le.trans hsmall
  exact (periodicizeBump_contDiff (fun _ : Fin 1 => -b) _ hw hs).comp (by fun_prop)

theorem periodicBranchChi_periodic (b δ : ℝ) (hδ : 0 < δ) :
    Function.Periodic (periodicBranchChi b δ hδ) (2*Real.pi) := by
  intro θ
  rw [periodicBranchChi_formula,periodicBranchChi_formula,
    show θ+2*Real.pi+b=(θ+b)+2*Real.pi by ring,periodicAngle_periodic]

theorem periodicBranchChi_local (b δ u : ℝ) (hδ : 0 < δ)
    (hu : -Real.pi < u) (hu' : u ≤ Real.pi) :
    periodicBranchChi b δ hδ (-b+u)=fixedBranchBump δ hδ u := by
  rw [periodicBranchChi_formula,show -b+u+b=u by ring,periodicAngle_eq hu hu']

theorem lowerChord_cos (b θ : ℝ) : lowerChord b θ=2-2*Real.cos (θ+b) := by
  unfold lowerChord
  rw [Real.cos_add]
  nlinarith [Real.sin_sq_add_cos_sq θ,Real.sin_sq_add_cos_sq b]

theorem periodicBranchChi_support_chord (b δ : ℝ) (hδ : 0 < δ) :
    tsupport (periodicBranchChi b δ hδ) ⊆ {θ | lowerChord b θ ≤ δ^2} := by
  apply closure_minimal
  · intro θ hθ
    change periodicBranchChi b δ hδ θ ≠ 0 at hθ
    rw [periodicBranchChi_formula] at hθ
    have hh := fixedBranchBump_support δ hδ hθ
    have hcos := Real.one_sub_sq_div_two_le_cos (x := periodicAngle (θ+b))
    rw [periodicAngle_cos] at hcos
    change lowerChord b θ ≤ δ^2
    rw [lowerChord_cos]
    have hp := mul_nonneg (sub_nonneg.mpr hh.le)
      (show 0 ≤ δ+|periodicAngle (θ+b)| by positivity)
    nlinarith [sq_abs (periodicAngle (θ+b))]
  · exact isClosed_le (by unfold lowerChord; fun_prop) continuous_const

/-- The actual closed periodic branch-cutoff support lies in an open true
plateau, so all cutoff derivatives retain m=1 and p=0 there. -/
theorem lowerM_plateau_on_periodic_branch_support (b η δ : ℝ)
    (hη : 0 < η) (hδ : 0 < δ) (hδη : δ < η) (θ : ℝ)
    (hθ : θ ∈ tsupport (periodicBranchChi b δ hδ)) :
    periodicLowerM b η =ᶠ[𝓝 θ] (fun _ => 1) := by
  have hchord : lowerChord b θ ≤ δ^2 := periodicBranchChi_support_chord b δ hδ hθ
  have hc : Continuous (lowerChord b) := by unfold lowerChord; fun_prop
  have hn : ∀ᶠ t in 𝓝 θ, lowerChord b t < η^2 :=
    hc.continuousAt.eventually (Iio_mem_nhds (by nlinarith))
  filter_upwards [hn] with t ht
  apply Real.smoothTransition.one_of_one_le
  have hh := (div_lt_one (show 0 < η^2 by positivity)).mpr ht
  linarith

theorem periodic_branch_jet_stays_on_m_plateau (b η δ : ℝ)
    (hη : 0 < η) (hδ : 0 < δ) (hδη : δ < η) (j : ℕ) (θ : ℝ)
    (hθ : θ ∈ tsupport (iteratedFDeriv ℝ j (periodicBranchChi b δ hδ))) :
    periodicLowerM b η =ᶠ[𝓝 θ] (fun _ => 1) :=
  lowerM_plateau_on_periodic_branch_support b η δ hη hδ hδη θ
    (tsupport_iteratedFDeriv_subset j hθ)

end
end IsingBulk.Tail
