import IsingBulk.HT22.Anchor.Field
import IsingBulk.Preferred22.AnchorFrameJets
namespace IsingBulk.HT22.Anchor
noncomputable section
open Set Filter Metric IsingBulk.Preferred22 IsingBulk.HT22.Geometry
open scoped Topology ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- Fixed-v parameter derivative written explicitly in moving-q variables. -/
def correctedUDot (s q : ℂ) : ℂ :=
  preferredSourceUDot s q-preferredSourceUQ s q*deriv preferredMovingBranch s

theorem correctedUDot_analyticAt (s q : ℂ)
    (hU : AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (s,q))
    (hb : AnalyticAt ℂ preferredMovingBranch s) :
    AnalyticAt ℂ (fun z : ℂ × ℂ => correctedUDot z.1 z.2) (s,q) := by
  have hd : AnalyticAt ℂ (fun z : ℂ × ℂ => deriv preferredMovingBranch z.1) (s,q) :=
    AnalyticAt.comp (f := fun z : ℂ × ℂ => z.1) (g := deriv preferredMovingBranch)
      hb.deriv analyticAt_fst
  exact (preferredSourceUDot_analyticAt_of_joint s q hU).sub
    ((preferredSourceUQ_analyticAt_of_joint s q hU).mul hd)

theorem correctedUDot_eq_inverseT (t v : ℂ)
    (hU : AnalyticAt ℂ (fun z : ℂ × ℂ => regularInverse z.1 z.2) (t,v))
    (hb : DifferentiableAt ℂ preferredMovingBranch t) :
    correctedUDot t (v-preferredMovingBranch t)=Geometry.inverseT t v := by
  change correctedUDot t (v-preferredMovingBranch t)=Tail.inverseT t v
  rw [Tail.inverseT_moving_adapter t v hU hb]
  simp only [correctedUDot,Tail.inverseV_moving_adapter]

/-- Actual uniform corrected scalar jets, including the named-anchor inverse
Uv. The branch-velocity term is retained rather than silently using UDot(q). -/
theorem actual_fixed_scalar_jets (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧
      ∀ B : PreferredCoareaBump d,B.delta<cap → ∀ δB : ℝ,0<δB →
      ∃ ε₀ τ₀ q₀ : ℝ,0<ε₀ ∧ 0<τ₀ ∧ 0≤q₀ ∧ q₀<1 ∧
      ∀ j : ℕ,∃ C : ℝ,1≤C ∧
      ∀ N : ℕ,0<N → ∀ ε τ : ℝ,0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
      ∀ θ : Fin N → ℝ,(∀ i,θ i∈Icc (-Real.pi-B.delta) B.delta) → ∀ i,
      let s := IsingBulk.Branch.radialParameter d.alpha ε
      let q := preferredSourceCoordinate τ B.p B.m s θ i
      ‖iteratedFDeriv ℂ j (fun z : ℂ × ℂ => preferredSourceUQ z.1 z.2) (s,q)‖≤C ∧
      ‖iteratedFDeriv ℂ j (fun z : ℂ × ℂ => correctedUDot z.1 z.2) (s,q)‖≤C ∧
      ‖iteratedFDeriv ℂ j (fun z : ℂ × ℂ => preferredOneBodyExtension z.1 z.2) (s,q)‖≤C ∧
      ‖iteratedFDeriv ℂ j (fun z : ℂ × ℂ => preferredRegularDiskRoot z.1 z.2) (s,q)‖≤C ∧
      (θ i≤ -d.b-δB/2 →
        ‖iteratedFDeriv ℂ j (fun z : ℂ × ℂ => (preferredSourceUQ z.1 z.2)⁻¹) (s,q)‖≤C ∧
        ‖preferredRegularDiskRoot s q‖≤q₀) := by
  obtain ⟨cap,hcap,hcapa,hdom⟩ := preferred_actual_whole_inverse_domain d
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hB δB hδB
  obtain ⟨D,L,ρ,κ,εd,τd,hD,hL,_hLD,hρ,hκ,hεd,hτd,hgood,hleft,hsource⟩ := hdom B hB δB hδB
  obtain ⟨rB,hrB,hBa⟩ := Metric.eventually_nhds_iff.mp
    (preferredMovingBranch_analyticAt_reference d).eventually_analyticAt
  let R := min ρ rB
  have hR : 0<R := lt_min hρ hrB
  let K := Metric.closedBall (preferredSelectedPoint d) (R/2) ×ˢ D
  let KL := Metric.closedBall (preferredSelectedPoint d) (R/2) ×ˢ L
  have hK : IsCompact K := (isCompact_closedBall _ _).prod hD
  have hKL : IsCompact KL := (isCompact_closedBall _ _).prod hL
  have hsr {s : ℂ} (hs : ‖s-preferredSelectedPoint d‖≤R/2) :
      ‖s-preferredSelectedPoint d‖<ρ ∧ AnalyticAt ℂ preferredMovingBranch s := by
    have hsR : ‖s-preferredSelectedPoint d‖<R := by linarith
    exact ⟨hsR.trans_le (min_le_left _ _),hBa (by
      rw [dist_eq_norm]
      exact hsR.trans_le (min_le_right _ _))⟩
  have hqa : AnalyticOnNhd ℂ (fun z : ℂ × ℂ => preferredSourceUQ z.1 z.2) K := by
    intro z hz
    have hs : ‖z.1-preferredSelectedPoint d‖≤R/2 := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz.1
    exact preferredSourceUQ_analyticAt_of_joint _ _ (hgood _ _ (hsr hs).1 hz.2).1
  have hsa : AnalyticOnNhd ℂ (fun z : ℂ × ℂ => correctedUDot z.1 z.2) K := by
    intro z hz
    have hs : ‖z.1-preferredSelectedPoint d‖≤R/2 := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz.1
    exact correctedUDot_analyticAt _ _ (hgood _ _ (hsr hs).1 hz.2).1 (hsr hs).2
  have haa : AnalyticOnNhd ℂ (fun z : ℂ × ℂ => preferredOneBodyExtension z.1 z.2) K := by
    intro z hz
    have hs : ‖z.1-preferredSelectedPoint d‖≤R/2 := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz.1
    exact (hgood _ _ (hsr hs).1 hz.2).2
  have hza : AnalyticOnNhd ℂ (fun z : ℂ × ℂ => preferredRegularDiskRoot z.1 z.2) K := by
    intro z hz
    have hs : ‖z.1-preferredSelectedPoint d‖≤R/2 := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz.1
    exact preferredRegularDiskRoot_analyticAt _ _ (hgood _ _ (hsr hs).1 hz.2).1 (hsr hs).2
  have hia : AnalyticOnNhd ℂ (fun z : ℂ × ℂ => (preferredSourceUQ z.1 z.2)⁻¹) KL := by
    intro z hz
    have hs : ‖z.1-preferredSelectedPoint d‖≤R/2 := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz.1
    have hg := hleft _ _ (hsr hs).1 hz.2
    exact (preferredSourceUQ_analyticAt_of_joint _ _ hg.2.1).inv hg.2.2.1
  obtain ⟨q₀,hq₀,hq₀1,hgap⟩ := preferred_compact_left_root_gap d L hL R hR
    (fun s q hs hq => hleft s q (hs.trans_le (min_le_left _ _)) hq)
  refine ⟨min εd (R/2),τd,q₀,lt_min hεd (half_pos hR),hτd,hq₀,hq₀1,?_⟩
  intro j
  obtain ⟨U,hU,hUj⟩ := preferred_compact_scalar_all_jets _ K hK hqa j
  obtain ⟨V,_hV,hVj⟩ := preferred_compact_scalar_all_jets _ K hK hsa j
  obtain ⟨A,_hA,hAj⟩ := preferred_compact_scalar_all_jets _ K hK haa j
  obtain ⟨Z,_hZ,hZj⟩ := preferred_compact_scalar_all_jets _ K hK hza j
  obtain ⟨I,_hI,hIj⟩ := preferred_compact_scalar_all_jets _ KL hKL hia j
  let C := max U (max V (max A (max Z I)))
  have hUC : U≤C := le_max_left _ _
  have hVC : V≤C := (le_max_left _ _).trans (le_max_right _ _)
  have hAC : A≤C := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hZC : Z≤C := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hIC : I≤C := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  refine ⟨C,hU.trans hUC,?_⟩
  intro N hN ε τ hε hεr hτ hτr θ hθ i
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  let q := preferredSourceCoordinate τ B.p B.m s θ i
  have hs : ‖s-preferredSelectedPoint d‖≤R/2 := by
    rw [preferred_radial_distance,abs_of_pos hε]
    exact (hεr.trans_le (min_le_right _ _)).le
  have hq := hsource N hN ε τ hε (hεr.trans_le (min_le_left _ _)) hτ hτr θ hθ i
  have hqD : q∈D := hq.1 (Metric.mem_closedBall_self hκ.le)
  have hz : (s,q)∈K := ⟨by simpa only [Metric.mem_closedBall,dist_eq_norm] using hs,hqD⟩
  refine ⟨(hUj _ hz).trans hUC,(hVj _ hz).trans hVC,(hAj _ hz).trans hAC,(hZj _ hz).trans hZC,?_⟩
  intro hi
  have hqL : q∈L := hq.2 hi (Metric.mem_closedBall_self hκ.le)
  exact ⟨(hIj (s,q) ⟨by simpa only [Metric.mem_closedBall,dist_eq_norm] using hs,hqL⟩).trans hIC,
    hgap s q hs hqL⟩

end
end IsingBulk.HT22.Anchor
