import IsingBulk.Tail.MixedActiveResidualJets
import IsingBulk.Tail.MicrocoreAmplitudeJets

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets Set Filter
open scoped Topology BigOperators
attribute [local fun_prop] analyticAt_fst analyticAt_snd

/-- One-body measure, inverse root, inverse contour coordinate. -/
def mixedBranchAmplitudeFactor (a : Fin 3) (s φ : ℂ) : ℂ :=
  if a=0 then (2*(Real.pi:ℂ))*microRegularOneBody s φ
  else if a=1 then Complex.exp (Complex.I*φ) else (regularY s φ)⁻¹

def mixedCompactAmplitudeFactor (a : Fin 3) (s y : ℂ) : ℂ :=
  if a=0 then y*residueFactor (selectedContinuedRoot s y)
  else if a=1 then (selectedContinuedRoot s y)⁻¹ else y⁻¹

theorem mixedBranchAmplitudeFactor_analytic_base (s : ℂ) (c : ℝ) (hs : s≠0)
    (hS : s+s⁻¹=(1+c:ℂ)) (hc : |c|<1) (a : Fin 3) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => mixedBranchAmplitudeFactor a p.1 p.2) (s,0) := by
  fin_cases a
  · exact analyticAt_const.mul (microRegularOneBody_analytic_base s c hs hS hc)
  · change AnalyticAt ℂ (fun p : ℂ × ℂ => Complex.exp (Complex.I*p.2)) (s,0)
    fun_prop
  · exact (regularY_analytic_base s c hs hS hc).inv (regularY_ne_zero s 0)

theorem mixedCompactAmplitudeFactor_analyticAt (a : Fin 3) {s y : ℂ}
    (h : (s,y)∈mixedRootPairDomain) :
    AnalyticAt ℂ (fun p : ℂ × ℂ => mixedCompactAmplitudeFactor a p.1 p.2) (s,y) := by
  have hz := selectedContinuedRoot_joint_analyticAt h.1 h.2.1 h.2.2
  have hn : selectedContinuedRoot s y≠0 := continuedRoot_nonzero _
  fin_cases a
  · change AnalyticAt ℂ (fun p : ℂ × ℂ => p.2*(2*(selectedContinuedRoot p.1 p.2)^2/
      (1-(selectedContinuedRoot p.1 p.2)^2))) (s,y)
    exact analyticAt_snd.mul ((analyticAt_const.mul (hz.pow 2)).div
      (analyticAt_const.sub (hz.pow 2)) (continuedRoot_residue_gap h.2.2))
  · exact hz.inv hn
  · exact analyticAt_snd.inv h.2.1

def mixedActiveAmplitudeVertex {N : ℕ} (J : Finset (Fin N)) (q : Fin N)
    (s : ℂ) (φ y : Fin N → ℂ) (a : Fin 3) (i : Fin N) : MixedActiveSpace N → ℂ :=
  if i∈J then mixedActiveBranch (mixedBranchAmplitudeFactor a) s φ i
  else mixedActiveCompact (mixedCompactAmplitudeFactor a) s y q i

theorem mixed_amplitude_vertex_jets (s₀ : ℂ) (c₀ : ℝ) (hs₀ : s₀≠0)
    (hS : s₀+s₀⁻¹=(1+c₀:ℂ)) (hc₀ : |c₀|<1) (order : ℕ) :
    ∃ U : Set (ℂ × ℂ),IsOpen U ∧ (s₀,0)∈U ∧
      ∀ K : Set (ℂ × ℂ),IsCompact K → K⊆mixedRootPairDomain → ∃ C : ℝ,0<C ∧
      ∀ (N : ℕ) (J : Finset (Fin N)) (q : Fin N) (s : ℂ) (φ y : Fin N → ℂ),
      (∀ i∈J,(s,φ i)∈U) → (∀ i∉J,(s,y i)∈K) →
      ∀ (a : Fin 3) (i : Fin N),JetBound (mixedActiveAmplitudeVertex J q s φ y a i) 0 order C := by
  obtain ⟨B,hB,hBb⟩ := finite_family_jet_bounds
    (fun a : Fin 3 => fun p : ℂ × ℂ => mixedBranchAmplitudeFactor a p.1 p.2)
    (s₀,0) (mixedBranchAmplitudeFactor_analytic_base s₀ c₀ hs₀ hS hc₀) order
  obtain ⟨U,hU,hUopen,hUbase⟩ := eventually_nhds_iff.mp hBb
  refine ⟨U,hUopen,hUbase,?_⟩
  intro K hK hKD
  have hcompact (a : Fin 3) : ∃ C : ℝ,0<C ∧ ∀ p∈K,∀ rotate : Bool,
      AnalyticAt ℂ (rotatingCompactCoefficient (mixedCompactAmplitudeFactor a) p.1 p.2 rotate) 0 ∧
      ∀ k≤order,‖iteratedFDeriv ℂ k (rotatingCompactCoefficient (mixedCompactAmplitudeFactor a) p.1 p.2 rotate) 0‖≤C :=
    compact_rotating_coefficient_uniform_jets K hK (mixedCompactAmplitudeFactor a)
      (fun p hp => mixedCompactAmplitudeFactor_analyticAt a (hKD hp)) order
  choose D hD hDb using hcompact
  let C := B+∑ a,D a
  have hBC : B≤C := le_add_of_nonneg_right (Finset.sum_nonneg (fun a _ => (hD a).le))
  have hDC (a : Fin 3) : D a≤C :=
    (Finset.single_le_sum (fun b _ => (hD b).le) (Finset.mem_univ a)).trans
      (le_add_of_nonneg_left (zero_le_one.trans hB))
  have hC : 0<C := (zero_lt_one.trans_le hB).trans_le hBC
  refine ⟨C,hC,?_⟩
  intro N J q s φ y hφ hy a i
  unfold mixedActiveAmplitudeVertex
  split_ifs with hi
  · have hh := hU _ (hφ i hi) a
    refine ⟨(mixedActiveBranch_jet_bound (mixedBranchAmplitudeFactor a) s φ i 0 hh.analytic).1,hC.le,?_⟩
    intro k hk
    exact (mixedActiveBranch_jet_bound (mixedBranchAmplitudeFactor a) s φ i k hh.analytic).2.trans
      ((hh.bound k hk).trans hBC)
  · have hh := hDb a (s,y i) (hy i hi) (decide (i=q))
    refine ⟨(mixedActiveCompact_jet_bound (mixedCompactAmplitudeFactor a) s y q i 0 hh.1).1,hC.le,?_⟩
    intro k hk
    exact (mixedActiveCompact_jet_bound (mixedCompactAmplitudeFactor a) s y q i k hh.1).2.trans
      ((hh.2 k hk).trans (hDC a))

end
end IsingBulk.Tail
