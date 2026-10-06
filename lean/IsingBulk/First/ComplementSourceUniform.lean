import IsingBulk.First.ComplementSourceAmplitudeSupport
import IsingBulk.First.ComplementSourcePhaseSmooth
import IsingBulk.First.ComplementClosedDamping
import IsingBulk.First.ComplementSimplex
import IsingBulk.First.ComplementUniform
import Mathlib.MeasureTheory.Group.Measure

/-! Uniform integration by parts instantiated with the actual source phase and
actual generated fixed-radius parameter-derivative amplitudes. -/
namespace IsingBulk.First
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local fun_prop] source_complexOfReal_contDiff

abbrev SourceIBPParameter {N : ℕ} (J : Finset (SingularFactorIndex N)) :=
  (ℝ × ℂ) × ((J → ℝ) × ℝ)

def sourceIBPPhase {N : ℕ} (J : Finset (SingularFactorIndex N))
    (p : SourceIBPParameter J) (u : DoubleAngularVector N) : ℂ :=
  sourcePhaseSum p.1.1 p.1.2 (fun _ => 1) (fun _ => 1) (fun f : J => f.1) p.2.1 u

def sourceIBPAmplitude {N : ℕ} (w : DoubleAngularVector N → ℝ)
    (J : Finset (SingularFactorIndex N)) (j : ℕ)
    (p : SourceIBPParameter J) (u : DoubleAngularVector N) : ℂ :=
  sourceNormalizedAmplitude (p.2.2 : ℂ) (dispersionAuxiliaryTotal (fun f : J => f.1) p.2.1 : ℂ)
    p.1.1 p.1.2 w J j u

theorem sourceIBPPhase_joint_contDiffAt {N : ℕ} (J : Finset (SingularFactorIndex N))
    (hJ : ∀ f ∈ J, validSourceFactor f) (p : SourceIBPParameter J) (u : DoubleAngularVector N)
    (hr : p.1.1 ≠ 0) (hs : p.1.2 ≠ 0) :
    ContDiffAt ℝ ∞ (fun q : SourceIBPParameter J × DoubleAngularVector N => sourceIBPPhase J q.1 q.2) (p,u) := by
  have h := sourcePhaseSum_joint_contDiffAt (fun f : J => f.1) (fun f => hJ f.1 f.2)
    p.1.1 p.1.2 p.2.1 u hr hs
  exact h.comp (p,u) (f := fun q : SourceIBPParameter J × DoubleAngularVector N =>
      ((q.1.1,q.1.2.1),q.2)) (by fun_prop)

theorem dispersionAuxiliaryTotal_contDiff {N : ℕ} {ι : Type*} [Fintype ι]
    (J : ι → SingularFactorIndex N) : ContDiff ℝ ∞ (dispersionAuxiliaryTotal J) := by
  unfold dispersionAuxiliaryTotal
  apply ContDiff.sum
  intro i _
  rcases J i with b | (k | a) <;> simp only
  · exact contDiff_const
  · exact contDiff_const
  · fun_prop

attribute [local fun_prop] dispersionAuxiliaryTotal_contDiff

theorem sourceIBPAmplitude_joint_contDiffAt {N : ℕ} (w : DoubleAngularVector N → ℝ)
    (hw : ContDiff ℝ ∞ w) (J : Finset (SingularFactorIndex N)) (j : ℕ)
    (p : SourceIBPParameter J) (u : DoubleAngularVector N)
    (hdom : (p.1,u) ∈ sourceInactiveDomain J) :
    ContDiffAt ℝ ∞ (fun q : SourceIBPParameter J × DoubleAngularVector N =>
      sourceIBPAmplitude w J j q.1 q.2) (p,u) := by
  have h := sourceNormalizedAmplitude_joint_contDiffAt w hw J
    (p.2.2 : ℂ) (dispersionAuxiliaryTotal (fun f : J => f.1) p.2.1 : ℂ)
    p.1.1 p.1.2 u hdom j
  exact h.comp (p,u) (f := fun q : SourceIBPParameter J × DoubleAngularVector N =>
      ((((q.1.2.2 : ℂ), (dispersionAuxiliaryTotal (fun f : J => f.1) q.1.2.1 : ℂ)),
        (q.1.1.1,q.2)),q.1.1.2)) (by fun_prop)


/-- On any compact source parameter family with the proved factor separator,
actual inactive-factor separation and physical damping, every fixed parameter
jet has arbitrary uniform integration-by-parts decay. Generated transpose
bounds and continuity are conclusions of ordinary smoothness and compactness. -/
theorem source_uniform_nonstationary_decay {N : ℕ} (w : DoubleAngularVector N → ℝ)
    (hw : ContDiff ℝ ∞ w) (J : Finset (SingularFactorIndex N))
    (hJ : ∀ f ∈ J, validSourceFactor f) {K : Set (SourceIBPParameter J)}
    {L : Set (DoubleAngularVector N)} (hK : IsCompact K) (hL : IsCompact L)
    (hsupp : tsupport w ⊆ L) (e : DoubleAngularVector N) (δ : ℝ) (hδ : 0 < δ)
    (hparam : ∀ p ∈ K, 0 < p.1.1 ∧ p.1.1 ≤ 1 ∧ p.1.2 ≠ 0 ∧
      p.1.1⁻¹-p.1.1 ≤ (sourceS p.1.2).im ∧ p.2.1 ∈ auxiliarySimplex J)
    (hden : ∀ p ∈ K, ∀ u ∈ L, ∀ f ∈ Jᶜ,
      sourceFactorDenominator p.1.2 (angleTuple p.1.1 u.1) (angleTuple p.1.1 u.2) f ≠ 0)
    (hsep : ∀ p ∈ K, ∀ u ∈ L, ∀ f ∈ J,
      δ ≤ angularDot e (dampedSingularVector p.1.1
        (torusShift (fun _ => 1) u.1) (torusShift (fun _ => 1) u.2) f))
    (j q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ∀ R : ℝ, 0 < R →
      ‖∫ u, sourceIBPAmplitude w J j p u * Complex.exp ((R : ℂ) * sourceIBPPhase J p u)‖ ≤
        R⁻¹ ^ q * C := by
  have hr (p) (hp : p ∈ K) : p.1.1 ≠ 0 := (hparam p hp).1.ne'
  have hs (p) (hp : p ∈ K) : p.1.2 ≠ 0 := (hparam p hp).2.2.1
  have hn (p) (hp : p ∈ K) (u) (hu : u ∈ L) : phaseDirection e (sourceIBPPhase J p) u ≠ 0 := by
    exact sourcePhaseSum_direction_ne_zero p.1.1 (hr p hp) p.1.2 _ _ (by simp) (by simp)
      (fun f : J => f.1) p.2.1 (hparam p hp).2.2.2.2.1 (hparam p hp).2.2.2.2.2
      u e hδ (fun f => hsep p hp u hu f.1 f.2)
  have hsup (p) : tsupport (sourceIBPAmplitude w J j p) ⊆ L :=
    (sourceNormalizedAmplitude_tsupport_subset _ _ _ _ w J j).trans hsupp
  let : (volume : Measure (DoubleAngularVector N)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure (volume : Measure (Fin N → ℝ)) (volume : Measure (Fin N → ℝ))
  apply uniform_nonstationary_decay hK hL e (sourceIBPPhase J) (sourceIBPAmplitude w J j)
  · intro p hp
    exact sourcePhaseSum_contDiff p.1.1 (hr p hp) p.1.2 _ _ (by simp) (by simp) _ _
  · intro p hp
    exact sourceNormalizedAmplitude_contDiff _ _ p.1.1 p.1.2 w hw J (hr p hp) (hs p hp)
      (fun u hu => hden p hp u (hsupp hu)) j
  · exact fun p _ => hsup p
  · exact fun p hp u hu => hn p hp u (hsup p hu)
  · intro p hp u _
    exact sourcePhaseSum_re_nonpositive_closed (hparam p hp).1 (hparam p hp).2.1
      (hparam p hp).2.2.2.1 _ _ (by simp) (by simp) _ _ (hparam p hp).2.2.2.2.1 u
  · exact continuousOn_parameterized_transposeIter e K L
      (fun p hp u _ => sourceIBPPhase_joint_contDiffAt J hJ p u (hr p hp) (hs p hp))
      (fun p hp u hu => sourceIBPAmplitude_joint_contDiffAt w hw J j p u
        ⟨hr p hp, hs p hp, hden p hp u hu⟩) hn q

end
end IsingBulk.First
