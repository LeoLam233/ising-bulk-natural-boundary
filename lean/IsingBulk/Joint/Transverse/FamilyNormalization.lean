import IsingBulk.Joint.Transverse.FamilyNormalizationLocal

/-! Common analytic transverse coordinates on genuine complex product disks.
This is the local family normalization required before applying compact-family
estimates. Both inverse identities retain the original family parameter. -/
namespace IsingBulk.Joint.Transverse
noncomputable section
open Set Filter Metric
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- One parameter-preserving inverse on a common product disk. The source and
inverse disks share a radius, chosen before the parameter or derivative order.
Centers off the selected edge may move; selected centers are fixed exactly. -/
structure FamilyNormalization (f : ℂ × E→ℂ) (eta₀ : E) where
  inverse : ℂ × E→ℂ
  radius : ℝ
  radius_pos : 0<radius
  analytic : ∀u eta, ‖u‖<radius → ‖eta-eta₀‖<radius → AnalyticAt ℂ inverse (u,eta)
  center : ∀eta, ‖eta-eta₀‖<radius → f (0,eta)=0 → inverse (0,eta)=0
  right_inv : ∀u eta, ‖u‖<radius → ‖eta-eta₀‖<radius → f (inverse (u,eta),eta)=u
  left_inv : ∀z eta, ‖z‖<radius → ‖eta-eta₀‖<radius → inverse (f (z,eta),eta)=z

/-- Genuine joint normalization of any nonramified scalar family, not merely
of physical ratio families. No inverse, common radius, or bound is assumed. -/
theorem exists_familyNormalization [CompleteSpace E] {f : ℂ × E→ℂ} {eta₀ : E}
    (hf : AnalyticAt ℂ f (0,eta₀)) (hzero : f (0,eta₀)=0)
    (hd : deriv (fun z=>f (z,eta₀)) 0≠0) : Nonempty (FamilyNormalization f eta₀) := by
  obtain ⟨e,he0,he,ha⟩ := familyEdgeMap_local_inverse hf hd
  have hF0 : familyEdgeMap f (0,eta₀)=(0,eta₀) := Prod.ext hzero rfl
  have hpa : AnalyticAt ℂ e.symm (0,eta₀) := by rwa [hF0] at ha
  have htarget : (0,eta₀)∈e.target := by
    have hh := e.map_source he0
    rwa [he,hF0] at hh
  have htarg : ∀ᶠq in 𝓝 (0,eta₀), q∈e.target := e.open_target.mem_nhds htarget
  have hsrc : ∀ᶠq in 𝓝 (0,eta₀), q∈e.source := e.open_source.mem_nhds he0
  have ht : ∀ᶠq in 𝓝 (0,eta₀), AnalyticAt ℂ e.symm q ∧ q∈e.target ∧ q∈e.source :=
    hpa.eventually_analyticAt.and (htarg.and hsrc)
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp ht
  have hq (u : ℂ) (eta : E) (hu : ‖u‖<r) (heta : ‖eta-eta₀‖<r) :
      AnalyticAt ℂ e.symm (u,eta) ∧ (u,eta)∈e.target ∧ (u,eta)∈e.source := by
    apply hball
    simpa only [mem_ball,dist_eq_norm,Prod.mk_sub_mk,Prod.norm_def,sub_zero] using max_lt hu heta
  refine ⟨{ inverse := fun q => (e.symm q).1
            radius := r
            radius_pos := hr
            analytic := ?_
            center := ?_
            right_inv := ?_
            left_inv := ?_ }⟩
  · intro u eta hu heta
    exact analyticAt_fst.comp (hq u eta hu heta).1
  · intro eta heta hz
    have hh := e.left_inv (hq 0 eta (by simpa using hr) heta).2.2
    rw [he] at hh
    have hf0 : familyEdgeMap f (0,eta)=(0,eta) := Prod.ext hz rfl
    rw [hf0] at hh
    exact congrArg Prod.fst hh
  · intro u eta hu heta
    have hh := e.right_inv (hq u eta hu heta).2.1
    rw [he] at hh
    have hs : (e.symm (u,eta)).2=eta := congrArg Prod.snd hh
    have hfst := congrArg Prod.fst hh
    change f ((e.symm (u,eta)).1,eta)=u
    change f (e.symm (u,eta))=u at hfst
    have hp : e.symm (u,eta)=((e.symm (u,eta)).1,eta) := Prod.ext rfl hs
    rw [hp] at hfst
    exact hfst
  · intro z eta hz heta
    have hh := e.left_inv (hq z eta hz heta).2.2
    rw [he] at hh
    exact congrArg Prod.fst hh

namespace FamilyNormalization
variable {f : ℂ × E→ℂ} {eta₀ : E} (N : FamilyNormalization f eta₀)

def normalizedFamily (curve : ℂ × E→Coupling) (q : ℂ × E) : Coupling :=
  curve (N.inverse q,q.2)

theorem normalized_center (curve : ℂ × E→Coupling) {eta : E}
    (heta : ‖eta-eta₀‖<N.radius) (hz : f (0,eta)=0) :
    N.normalizedFamily curve (0,eta)=curve (0,eta) := by
  simp only [normalizedFamily,N.center eta heta hz]

theorem normalized_analyticAt_center (curve : ℂ × E→Coupling) {eta : E}
    (heta : ‖eta-eta₀‖<N.radius) (hz : f (0,eta)=0)
    (hc : AnalyticAt ℂ curve (0,eta)) : AnalyticAt ℂ (N.normalizedFamily curve) (0,eta) := by
  have hi := (N.analytic 0 eta (by simpa using N.radius_pos) heta).prod analyticAt_snd
  exact hc.comp_of_eq hi (Prod.ext (N.center eta heta hz) rfl)

theorem original_recovered (curve : ℂ × E→Coupling) {z : ℂ} {eta : E}
    (hz : ‖z‖<N.radius) (heta : ‖eta-eta₀‖<N.radius) :
    N.normalizedFamily curve (f (z,eta),eta)=curve (z,eta) := by
  simp only [normalizedFamily,N.left_inv z eta hz heta]

theorem right_inv_germ {eta : E} (heta : ‖eta-eta₀‖<N.radius) :
    ∀ᶠu : ℂ in 𝓝 0,f (N.inverse (u,eta),eta)=u := by
  filter_upwards [Metric.ball_mem_nhds (0:ℂ) N.radius_pos] with u hu
  exact N.right_inv u eta (mem_ball_zero_iff.mp hu) heta

end FamilyNormalization
end
end IsingBulk.Joint.Transverse
