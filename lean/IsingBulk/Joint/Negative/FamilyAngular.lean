import IsingBulk.Joint.Negative.FamilyIdentities
import IsingBulk.Anisotropic.NegativeNormalForm.UniformAngularComparison

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric IsingBulk.Anisotropic.NegativeNormalForm
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Arbitrarily small angular Lipschitz control on one common tridisk for a
compact genuinely complex family. -/
theorem compact_family_angular_small (B : ℂ × E→ℂ) (phi : ℝ) (hphi : Real.sin phi≠0)
    {P : Set E} (hP : IsCompact P) (hB : ∀eta∈P,AnalyticAt ℂ B (0,eta))
    (ε : ℝ) (hε : 0<ε) :
    ∃δ : ℝ,0<δ ∧ ∀eta∈P,∀t d x y : ℂ,
      ‖t‖<δ → ‖d‖<δ → ‖x‖<δ → ‖y‖<δ →
      ‖negativePhase (familyMember B eta) phi hphi t (d+x)-
        negativePhase (familyMember B eta) phi hphi t (d+y)‖≤ε*‖x-y‖ := by
  let F : ScalarTriple×E→ℂ := fun q=>
    phaseFirstFactor (familyMember B q.2) phi hphi q.1.2.1 q.1.1 q.1.2.2
  let U : Set (ScalarTriple×E) := {q | AnalyticAt ℂ F q ∧ ‖F q‖<ε}
  have hU : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro q hq
    exact hq.1.eventually_analyticAt.and (hq.1.continuousAt.norm.eventually_lt_const hq.2)
  obtain ⟨r0,hr0,hbound⟩ := compact_product_tube hP hU (by
    intro eta heta
    exact ⟨family_phaseFirstFactor_analyticAt B phi hphi eta (hB eta heta),
      by change ‖phaseFirstFactor (familyMember B eta) phi hphi 0 0 0‖<ε
         simpa only [phaseFirstFactor_origin,norm_zero] using hε⟩)
  obtain ⟨r1,hr1,hidentity⟩ := compact_family_factor_identities B phi hphi hP hB
  let r := min r0 r1
  have hr : 0<r := lt_min hr0 hr1
  refine ⟨r/4,by positivity,?_⟩
  intro eta heta t d x y ht hd hx hy
  have hinput : ‖(t,(d+y,x-y))‖<r := by
    change max ‖t‖ (max ‖d+y‖ ‖x-y‖)<r
    have hdy := norm_add_le d y
    have hxy := norm_sub_le x y
    exact max_lt (by linarith) (max_lt (by linarith) (by linarith))
  have hb := (hbound eta heta (t,(d+y,x-y)) (hinput.trans_le (min_le_left _ _))).2
  have hi := (hidentity eta heta (t,(d+y,x-y)) (hinput.trans_le (min_le_right _ _))).1
  have hid : d+y+(x-y)=d+x := by ring
  simp only [phaseIncrement,hid] at hi
  rw [hi,norm_mul]
  exact (mul_le_mul_of_nonneg_left hb.le (norm_nonneg _)).trans_eq (mul_comm _ _)

end
end IsingBulk.Joint.Negative
