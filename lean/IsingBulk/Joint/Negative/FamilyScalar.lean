import IsingBulk.Joint.Negative.CompactAnalyticBounds
import IsingBulk.Anisotropic.NegativeNormalForm.UniformPhaseSlope

/-! Compact complex-family control of the actual scalar pole slope. -/
namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric
open scoped Topology
open IsingBulk.Anisotropic.NegativeNormalForm IsingBulk.First

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def familyMember (B : ℂ × E → ℂ) (eta : E) (t : ℂ) : ℂ := B (t, eta)

theorem familyMember_analyticAt {B : ℂ × E → ℂ} {eta : E}
    (hB : AnalyticAt ℂ B (0, eta)) : AnalyticAt ℂ (familyMember B eta) 0 :=
  hB.comp (f := fun t : ℂ => (t, eta)) (analyticAt_id.prod analyticAt_const)

/-- Reassociation makes t the differentiation parameter and leaves both the
angle and the genuinely complex family parameter independent. -/
def parameterFamilyPhase (B : ℂ × E → ℂ) (phi : ℝ) (hphi : Real.sin phi ≠ 0)
    (q : ℂ × (ℂ × E)) : ℂ := familyPhase B phi hphi ((q.1, q.2.1), q.2.2)

theorem parameterFamilyPhase_analyticAt_center {B : ℂ × E → ℂ} {eta : E}
    (phi : ℝ) (hphi : Real.sin phi ≠ 0) (hB : AnalyticAt ℂ B (0, eta)) :
    AnalyticAt ℂ (parameterFamilyPhase B phi hphi) (0, (0, eta)) := by
  apply (familyPhase_analyticAt_center B phi hphi eta hB).comp
    (f := fun q : ℂ × (ℂ × E) => ((q.1, q.2.1), q.2.2))
  exact (analyticAt_fst.prod (analyticAt_fst.comp analyticAt_snd)).prod
    (analyticAt_snd.comp analyticAt_snd)

/-- The parameter derivative is itself a jointly analytic family. -/
def familySlope (B : ℂ × E → ℂ) (phi : ℝ) (hphi : Real.sin phi ≠ 0)
    (q : (ℂ × ℂ) × E) : ℂ :=
  jointParameterJet (parameterFamilyPhase B phi hphi) 1 (q.1.1, (q.1.2, q.2))

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
@[simp] theorem familySlope_eq (B : ℂ × E → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) (t d : ℂ) (eta : E) :
    familySlope B phi hphi ((t,d),eta) = phaseParameterSlope (familyMember B eta) phi hphi (t,d) := by
  rw [familySlope, jointParameterJet_eq, phaseParameterSlope_eq]
  rfl

theorem familySlope_analyticAt_center {B : ℂ × E → ℂ} {eta : E}
    (phi : ℝ) (hphi : Real.sin phi ≠ 0) (hB : AnalyticAt ℂ B (0, eta)) :
    AnalyticAt ℂ (familySlope B phi hphi) ((0,0),eta) := by
  apply (jointParameterJet_analyticAt (parameterFamilyPhase_analyticAt_center phi hphi hB) 1).comp
    (f := fun q : (ℂ × ℂ) × E => (q.1.1, (q.1.2, q.2)))
  exact (analyticAt_fst.comp analyticAt_fst).prod
    ((analyticAt_snd.comp analyticAt_fst).prod analyticAt_snd)

/-- Relative slope separation with one common bidisk for the entire compact
complex parameter family. This is the contraction input for all dimensions. -/
theorem compact_family_uniform_slope (B : ℂ × E → ℂ) (phi : ℝ)
    (hphi : Real.sin phi ≠ 0) {K : Set E} (hK : IsCompact K)
    (hB : ∀ eta ∈ K, AnalyticAt ℂ B (0, eta))
    (hn : ∀ eta ∈ K, B (0, eta) ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ eta ∈ K, ∀ t d : ℂ, ‖t‖ < r → ‖d‖ < r →
      AnalyticAt ℂ (fun q : ℂ × ℂ => negativePhase (familyMember B eta) phi hphi q.1 q.2) (t,d) ∧
      ‖phaseParameterSlope (familyMember B eta) phi hphi (t,d) -
        centralParameterSlope (familyMember B eta) phi 0‖ ≤
        ‖centralParameterSlope (familyMember B eta) phi 0‖ / 4 := by
  let c : E → ℂ := fun eta => centralParameterSlope (familyMember B eta) phi 0
  let U : Set ((ℂ × ℂ) × E) := {q |
    AnalyticAt ℂ (familyPhase B phi hphi) q ∧
    AnalyticAt ℂ (familySlope B phi hphi) q ∧ AnalyticAt ℂ c q.2 ∧
    ‖familySlope B phi hphi q - c q.2‖ < ‖c q.2‖ / 4}
  have hca (eta : E) (ha : AnalyticAt ℂ B (0, eta)) : AnalyticAt ℂ c eta := by
    simp only [c, centralParameterSlope, Complex.cos_zero, sub_self, familyMember]
    exact analyticAt_const.mul (ha.comp (f := fun eta : E => (0,eta))
      (analyticAt_const.prod analyticAt_id))
  have hU : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro q hq
    have hc : ContinuousAt (fun p : (ℂ × ℂ) × E => c p.2) q :=
      hq.2.2.1.continuousAt.comp continuous_snd.continuousAt
    have hlt := ((hq.2.1.continuousAt.sub hc).norm).eventually_lt
      (hc.norm.div_const 4) hq.2.2.2
    have hce := continuous_snd.continuousAt.tendsto.eventually hq.2.2.1.eventually_analyticAt
    exact hq.1.eventually_analyticAt.and (hq.2.1.eventually_analyticAt.and (hce.and hlt))
  obtain ⟨r, hr, htube⟩ := compact_product_tube hK hU (by
    intro eta heta
    refine ⟨familyPhase_analyticAt_center B phi hphi eta (hB eta heta),
      familySlope_analyticAt_center phi hphi (hB eta heta), hca eta (hB eta heta), ?_⟩
    have hcn : c eta ≠ 0 := centralParameterSlope_ne_zero (familyMember B eta) phi hphi 0
      (by simpa only [Complex.cos_zero, sub_self, familyMember] using hn eta heta)
    change ‖familySlope B phi hphi ((0,0),eta) - c eta‖ < ‖c eta‖ / 4
    rw [familySlope_eq, phaseParameterSlope_origin _ phi hphi (familyMember_analyticAt (hB eta heta))]
    change ‖c eta - c eta‖ < ‖c eta‖ / 4
    rw [sub_self, norm_zero]
    exact div_pos (norm_pos_iff.mpr hcn) (by norm_num))
  refine ⟨r, hr, ?_⟩
  intro eta heta t d ht hd
  obtain ⟨hphase, hslope, _hc, hbound⟩ := htube eta heta (t,d)
    (by simpa only [Prod.norm_def, max_lt_iff] using And.intro ht hd)
  refine ⟨?_, ?_⟩
  · exact hphase.comp (f := fun q : ℂ × ℂ => (q,eta))
      (analyticAt_id.prod analyticAt_const)
  · simpa only [familySlope_eq] using hbound.le

end
end IsingBulk.Joint.Negative
