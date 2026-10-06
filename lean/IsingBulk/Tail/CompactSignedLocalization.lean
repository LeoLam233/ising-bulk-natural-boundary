import IsingBulk.Tail.CompactSectorNumeratorJets
import IsingBulk.Tail.CompactRightSectorGeometry

/-! The right sector is supported strictly inside the signed fundamental
cube. Its zero extension is smooth, with exactly the original local jets. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter Function MeasureTheory
open scoped Topology ContDiff

def compactSignedWeight {N : ℕ} (w : (Fin N → ℝ) → ℂ) : (Fin N → ℝ) → ℂ :=
  (signedAngleBox N).indicator w

theorem compactSignedWeight_tsupport {N : ℕ} (w : (Fin N → ℝ) → ℂ) {R : ℝ}
    (hsupp : tsupport w ∩ signedAngleBox N ⊆ Icc (fun _ => -R) (fun _ => R)) :
    tsupport (compactSignedWeight w) ⊆ Icc (fun _ => -R) (fun _ => R) := by
  apply closure_minimal _ isClosed_Icc
  intro θ hθ
  by_cases hb : θ ∈ signedAngleBox N
  · apply hsupp ⟨subset_tsupport w ?_,hb⟩
    change (signedAngleBox N).indicator w θ ≠ 0 at hθ
    rwa [indicator_of_mem hb] at hθ
  · exact False.elim (hθ (by simp [compactSignedWeight,hb]))

theorem compactSignedWeight_germ {N : ℕ} (w : (Fin N → ℝ) → ℂ) {R : ℝ}
    (hR : R < Real.pi) {θ : Fin N → ℝ} (hθ : θ ∈ Icc (fun _ => -R) (fun _ => R)) :
    compactSignedWeight w =ᶠ[𝓝 θ] w := by
  have hb : signedAngleBox N ∈ 𝓝 θ := pi_Icc_mem_nhds
    (fun i => lt_of_lt_of_le (by linarith : -Real.pi < -R) (hθ.1 i))
    (fun i => (hθ.2 i).trans_lt hR)
  filter_upwards [hb] with x hx
  exact indicator_of_mem hx w

theorem compactSignedWeight_smooth {N : ℕ} (w : (Fin N → ℝ) → ℂ) (hw : ContDiff ℝ ∞ w)
    {R : ℝ} (hR : R < Real.pi)
    (hsupp : tsupport w ∩ signedAngleBox N ⊆ Icc (fun _ => -R) (fun _ => R)) :
    ContDiff ℝ ∞ (compactSignedWeight w) ∧ HasCompactSupport (compactSignedWeight w) := by
  have hsupport := compactSignedWeight_tsupport w hsupp
  refine ⟨?_,isCompact_Icc.of_isClosed_subset isClosed_closure hsupport⟩
  rw [contDiff_iff_contDiffAt]
  intro θ
  by_cases hθ : θ ∈ Icc (fun _ => -R) (fun _ => R)
  · exact hw.contDiffAt.congr_of_eventuallyEq (compactSignedWeight_germ w hR hθ)
  · exact contDiffAt_const.congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp (fun h => hθ (hsupport h)))

theorem compactSignedWeight_integral {N : ℕ} (w F : (Fin N → ℝ) → ℂ) :
    (∫ θ, compactSignedWeight w θ*F θ)=∫ θ in signedAngleBox N, w θ*F θ := by
  rw [← integral_indicator (show MeasurableSet (signedAngleBox N) from measurableSet_Icc)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun θ => by
    by_cases hθ : θ ∈ signedAngleBox N <;> simp [compactSignedWeight,hθ])

theorem compactSignedWeight_mul_jets {N J : ℕ} (w : (Fin N → ℝ) → ℂ)
    (A : ℂ × (Fin N → ℝ) → ℂ) {R ρ C : ℝ} {a : ℤ} (hR : R < Real.pi)
    (hsupp : tsupport w ∩ signedAngleBox N ⊆ Icc (fun _ => -R) (fun _ => R))
    (hρ : 0 ≤ ρ) (hC : 0 ≤ C) (p : ℂ × (Fin N → ℝ))
    (hb : p.2 ∈ Icc (fun _ => -R) (fun _ => R) →
      RealScaledJetBound (fun q => w q.2*A q) p J ρ C a) :
    RealScaledJetBound (fun q => compactSignedWeight w q.2*A q) p J ρ C a := by
  by_cases hp : p.2 ∈ Icc (fun _ => -R) (fun _ => R)
  · apply (hb hp).congr
    have he := (compactSignedWeight_germ w hR hp).comp_tendsto continuous_snd.continuousAt.tendsto
    filter_upwards [he] with q hq
    rw [show compactSignedWeight w q.2=w q.2 from hq]
  · exact angular_weighted_zero_jets _ A
      (fun hn => hp (compactSignedWeight_tsupport w hsupp hn)) hρ hC a

theorem nested_all_right_signed_support {N : ℕ} (b outer inner : ℝ) (ho : 0 < outer)
    (hi : 0 < inner) (q : Fin N) (sigma : Fin N → Fin 3) (hsigma : ∀ i, sigma i=1)
    {θ : Fin N → ℝ} (hθ : θ ∈ tsupport (nestedSectorWeight b outer inner ho hi q sigma))
    (hbox : θ ∈ signedAngleBox N) :
    θ ∈ Icc (fun _ => -rightSectorRadius b inner) (fun _ => rightSectorRadius b inner) := by
  have hassign : θ ∈ tsupport (sectorAssignmentWeight b inner hi sigma) := tsupport_mul_subset_right hθ
  have hr (i : Fin N) : |θ i| ≤ rightSectorRadius b inner := by
    have hh := sector_assignment_tsupport b inner hi sigma hassign i
    have he : sectorLabel b inner hi (sigma i)=sectorRight b inner hi := by
      rw [hsigma i]
      funext x
      simp [sectorLabel]
    rw [he] at hh
    have hh' : θ i ∈ tsupport (sectorRight b inner hi) := hh
    exact right_sector_signed_interval (abs_le.mpr ⟨hbox.1 i,hbox.2 i⟩) ((sector_labels_tsupport b inner hi).2.1 hh')
  exact ⟨fun i => (abs_le.mp (hr i)).1,fun i => (abs_le.mp (hr i)).2⟩

theorem original_all_right_signed_support {N : ℕ} (f : SelectorFunctions)
    (b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner) (q : Fin N)
    (sigma : Fin N → Fin 3) (hsigma : ∀ i, sigma i=1) :
    tsupport (originalSectorAngularWeight f b outer inner ho hi q sigma) ∩ signedAngleBox N ⊆
      Icc (fun _ => -rightSectorRadius b inner) (fun _ => rightSectorRadius b inner) := by
  intro θ hθ
  exact nested_all_right_signed_support b outer inner ho hi q sigma hsigma
    (tsupport_comp_subset (g := Complex.ofReal) (by simp) _ (tsupport_mul_subset_right hθ.1)) hθ.2

theorem current_all_right_signed_support {N : ℕ} (f : SelectorFunctions)
    (τ b outer inner : ℝ) (ho : 0 < outer) (hi : 0 < inner) (qS q : Fin N)
    (sigma : Fin N → Fin 3) (hsigma : ∀ i, sigma i=1) :
    tsupport (currentSectorAngularWeight f τ qS b outer inner ho hi q sigma) ∩ signedAngleBox N ⊆
      Icc (fun _ => -rightSectorRadius b inner) (fun _ => rightSectorRadius b inner) := by
  intro θ hθ
  exact nested_all_right_signed_support b outer inner ho hi q sigma hsigma
    (tsupport_comp_subset (g := Complex.ofReal) (by simp) _ (tsupport_mul_subset_right hθ.1)) hθ.2

end
end IsingBulk.Tail
