import IsingBulk.Tail.SelectorDefinitions
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Constructed periodic upper selectors and a genuinely localized lower
chord bump. Thresholds are fixed geometric parameters, not ε- or N-dependent.
Attachment to the exact endpoint-width convention is stated separately. -/
namespace IsingBulk.Tail
noncomputable section
open Set Filter
open scoped Topology ContDiff

def thresholdStep (l h x : ℝ) : ℝ := Real.smoothTransition ((x-l)/(h-l))

def periodicUpperA (α θ : ℝ) : ℝ := thresholdStep α (3*α/2) (Real.sin θ)
def periodicUpperP (α θ : ℝ) : ℝ := thresholdStep (α/2) (3*α/4) (Real.sin θ)

def lowerChord (b θ : ℝ) : ℝ :=
  (Real.cos θ-Real.cos b)^2+(Real.sin θ+Real.sin b)^2

def periodicLowerM (b η θ : ℝ) : ℝ :=
  Real.smoothTransition (2-lowerChord b θ/η^2)

def constructedSelector (b η α : ℝ) : SelectorFunctions :=
  ⟨periodicUpperP α,periodicLowerM b η,periodicUpperA α⟩

theorem thresholdStep_range (l h x : ℝ) :
    0 ≤ thresholdStep l h x ∧ thresholdStep l h x ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩

theorem thresholdStep_zero {l h x : ℝ} (hlh : l < h) (hx : x ≤ l) :
    thresholdStep l h x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) (sub_pos.mpr hlh).le

theorem thresholdStep_one {l h x : ℝ} (hlh : l < h) (hx : h ≤ x) :
    thresholdStep l h x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  exact (one_le_div (sub_pos.mpr hlh)).mpr (by linarith)

theorem periodicUpperA_smooth (α : ℝ) : ContDiff ℝ ∞ (periodicUpperA α) := by
  unfold periodicUpperA thresholdStep
  fun_prop

theorem periodicUpperP_smooth (α : ℝ) : ContDiff ℝ ∞ (periodicUpperP α) := by
  unfold periodicUpperP thresholdStep
  fun_prop

theorem periodicLowerM_smooth (b η : ℝ) : ContDiff ℝ ∞ (periodicLowerM b η) := by
  unfold periodicLowerM lowerChord
  fun_prop

theorem constructedSelector_periodic (b η α θ : ℝ) :
    periodicUpperA α (θ+2*Real.pi)=periodicUpperA α θ ∧
    periodicUpperP α (θ+2*Real.pi)=periodicUpperP α θ ∧
    periodicLowerM b η (θ+2*Real.pi)=periodicLowerM b η θ := by
  simp [periodicUpperA,periodicUpperP,periodicLowerM,lowerChord]

theorem upperA_support_sine (α : ℝ) (hα : 0 < α) :
    tsupport (periodicUpperA α) ⊆ {θ | α ≤ Real.sin θ} := by
  apply closure_minimal
  · intro θ hθ
    by_contra hn
    have he : periodicUpperA α θ = 0 := thresholdStep_zero (by linarith) (le_of_lt (lt_of_not_ge hn))
    exact hθ he
  · exact isClosed_le continuous_const Real.continuous_sin

/-- p=1 on an open neighborhood of the entire closed a-support. Thus
its derivatives vanish there, including on every finite a-jet support. -/
theorem upperP_plateau_on_a_support (α : ℝ) (hα : 0 < α) (θ : ℝ)
    (hθ : θ ∈ tsupport (periodicUpperA α)) :
    periodicUpperP α =ᶠ[𝓝 θ] (fun _ => 1) := by
  have hsin : α ≤ Real.sin θ := upperA_support_sine α hα hθ
  have hn : ∀ᶠ t in 𝓝 θ, 3*α/4 < Real.sin t :=
    Real.continuous_sin.continuousAt.eventually (Ioi_mem_nhds (by linarith))
  filter_upwards [hn] with t ht
  exact thresholdStep_one (by linarith) ht.le

theorem lowerM_support_chord (b η : ℝ) (hη : 0 < η) :
    tsupport (periodicLowerM b η) ⊆ {θ | lowerChord b θ ≤ 2*η^2} := by
  apply closure_minimal
  · intro θ hθ
    by_contra hn
    have hgt : 2*η^2 < lowerChord b θ := lt_of_not_ge hn
    have hz : 2-lowerChord b θ/η^2 ≤ 0 := by
      have hd := (lt_div_iff₀ (show 0 < η^2 by positivity)).mpr hgt
      linarith
    exact hθ (Real.smoothTransition.zero_of_nonpos hz)
  · exact isClosed_le (by unfold lowerChord; fun_prop) continuous_const

/-- The lower bump is actually localized and stays a fixed distance below
both real-axis endpoints; its support cannot meet any upper selector. -/
theorem lowerM_support_negative (b η : ℝ) (hb : 0 < Real.sin b)
    (hη : 0 < η) (hηsmall : η ≤ Real.sin b/4) (θ : ℝ)
    (hθ : θ ∈ tsupport (periodicLowerM b η)) :
    Real.sin θ < -Real.sin b/2 := by
  have hh : lowerChord b θ ≤ 2*η^2 := lowerM_support_chord b η hη hθ
  unfold lowerChord at hh
  have hsq := sq_nonneg (Real.cos θ-Real.cos b)
  have hηsq : η^2 ≤ (Real.sin b)^2/16 := by nlinarith
  nlinarith [sq_nonneg (Real.sin θ+Real.sin b/2)]

/-- A genuine open plateau contains the lower branch center. -/
theorem lowerM_plateau_near_center (b η : ℝ) (hη : 0 < η) :
    periodicLowerM b η =ᶠ[𝓝 (-b)] (fun _ => 1) := by
  have hc : Continuous (lowerChord b) := by unfold lowerChord; fun_prop
  have hz : lowerChord b (-b)=0 := by simp [lowerChord]
  have hn : ∀ᶠ θ in 𝓝 (-b), lowerChord b θ < η^2 :=
    hc.continuousAt.eventually (Iio_mem_nhds (by rw [hz]; positivity))
  filter_upwards [hn] with θ hθ
  apply Real.smoothTransition.one_of_one_le
  have hh := (div_lt_one (show 0 < η^2 by positivity)).mpr hθ
  linarith

theorem upperP_support_sine (α : ℝ) (hα : 0 < α) :
    tsupport (periodicUpperP α) ⊆ {θ | α/2 ≤ Real.sin θ} := by
  apply closure_minimal
  · intro θ hθ
    by_contra hn
    have he : periodicUpperP α θ = 0 := thresholdStep_zero (by linarith) (le_of_lt (lt_of_not_ge hn))
    exact hθ he
  · exact isClosed_le continuous_const Real.continuous_sin

theorem lowerM_zero_of_nonneg_sine (b η θ : ℝ) (hb : 0 < Real.sin b)
    (hη : 0 < η) (hηsmall : η ≤ Real.sin b/4) (hθ : 0 ≤ Real.sin θ) :
    periodicLowerM b η θ = 0 := by
  by_contra he
  have hs : θ ∈ tsupport (periodicLowerM b η) := subset_closure he
  linarith [lowerM_support_negative b η hb hη hηsmall θ hs]

/-- Reflected lower-bump support lies strictly inside the upper a=1 plateau,
not merely at a cutoff endpoint. -/
theorem reflected_lowerM_upperA_plateau (b η α θ : ℝ)
    (hb : 0 < Real.sin b) (hη : 0 < η) (hηsmall : η ≤ Real.sin b/4)
    (hα : 0 < α) (hαsmall : α < Real.sin b/4)
    (hθ : θ ∈ tsupport (periodicLowerM b η)) :
    periodicUpperA α =ᶠ[𝓝 (-θ)] (fun _ => 1) := by
  have hn := lowerM_support_negative b η hb hη hηsmall θ hθ
  have hs : 2*α < Real.sin (-θ) := by rw [Real.sin_neg]; linarith
  have he : ∀ᶠ t in 𝓝 (-θ), 2*α < Real.sin t :=
    Real.continuous_sin.continuousAt.eventually (Ioi_mem_nhds hs)
  filter_upwards [he] with t ht
  exact thresholdStep_one (by linarith) (by linarith)

/-- The fixed p and m supports are disjoint, so occupancy coupling cannot
produce a diagonal m p' contribution on their plateau neighborhoods. -/
theorem constructed_selector_supports_disjoint (b η α : ℝ)
    (hb : 0 < Real.sin b) (hη : 0 < η) (hηsmall : η ≤ Real.sin b/4)
    (hα : 0 < α) :
    Disjoint (tsupport (periodicUpperP α)) (tsupport (periodicLowerM b η)) := by
  apply Set.disjoint_left.mpr
  intro θ hp hm
  have hpos : α/2 ≤ Real.sin θ := upperP_support_sine α hα hp
  have hneg := lowerM_support_negative b η hb hη hηsmall θ hm
  linarith

/-- m vanishes on an open neighborhood of every named a-support point. -/
theorem lowerM_zero_near_a_support (b η α θ : ℝ)
    (hb : 0 < Real.sin b) (hη : 0 < η) (hηsmall : η ≤ Real.sin b/4)
    (hα : 0 < α) (hθ : θ ∈ tsupport (periodicUpperA α)) :
    periodicLowerM b η =ᶠ[𝓝 θ] (fun _ => 0) := by
  have hpos : α ≤ Real.sin θ := upperA_support_sine α hα hθ
  have he : ∀ᶠ t in 𝓝 θ, 0 < Real.sin t :=
    Real.continuous_sin.continuousAt.eventually (Ioi_mem_nhds (by linarith))
  filter_upwards [he] with t ht
  exact lowerM_zero_of_nonneg_sine b η t hb hη hηsmall ht.le

end
end IsingBulk.Tail
