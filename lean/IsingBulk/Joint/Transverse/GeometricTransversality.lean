import IsingBulk.Joint.Transverse.SymmetryTransport
import IsingBulk.Joint.Transverse.NegativeEvenObstruction
import IsingBulk.Joint.Geometry.Conjugation

/-! # Literal nonramified transversality to a regular complex edge
At a regular point the unsquared real coefficients are unique. The condition
below says that the actual defining equation has nonzero derivative, and is
invariant under the two physical symmetries.
-/
namespace IsingBulk.Joint.Transverse
noncomputable section
open Set Filter
open scoped Topology

def edgeEquation (a b : ℝ) (K : Coupling) : ℂ := A K-S K*(a:ℂ)-T K*(b:ℂ)

def IsNonramifiedJointTransversal (c : ℂ→Coupling) (z : ℂ) : Prop :=
  ∀ a b : ℝ, edgeEquation a b (c z)=0 →
    ((a = -1 ∨ a = 1) ∨ (b = -1 ∨ b = 1)) →
    deriv (fun t => edgeEquation a b (c t)) z≠0

/-- At a regular point the universal formulation is exactly the ordinary
nonzero derivative of any one genuine edge defining equation. -/
theorem nonramified_iff_edge_deriv {c : ℂ→Coupling} {z : ℂ} {a b : ℝ}
    (hS : S (c z)≠0) (hB : (transferB (c z)).im≠0)
    (he : edgeEquation a b (c z)=0)
    (hab : (a = -1 ∨ a = 1) ∨ (b = -1 ∨ b = 1)) :
    IsNonramifiedJointTransversal c z ↔ deriv (fun t => edgeEquation a b (c t)) z≠0 := by
  have uniq (r s : ℝ) (he : edgeEquation r s (c z)=0) :
      faceA (c z)=r ∧ faceB (c z)=s := by
    apply transfer_face_coordinates_unique hB
    dsimp [edgeEquation] at he
    unfold transferC transferB
    field_simp
    linear_combination he
  constructor
  · intro ht
    exact ht a b he hab
  · intro hd r s hrs _
    have h₁ := uniq a b he
    have h₂ := uniq r s hrs
    have hr : r=a := h₂.1.symm.trans h₁.1
    have hs : s=b := h₂.2.symm.trans h₁.2
    simpa only [hr,hs] using hd

@[simp] theorem edgeEquation_swap (a b : ℝ) (K : Coupling) :
    edgeEquation a b K.swap=edgeEquation b a K := by
  dsimp [edgeEquation,A,S,T]
  ring

@[simp] theorem edgeEquation_star (a b : ℝ) (K : Coupling) :
    edgeEquation a b (star K)=star (edgeEquation a b K) := by simp [edgeEquation]

theorem IsNonramifiedJointTransversal.swap {c : ℂ→Coupling} {z : ℂ}
    (ht : IsNonramifiedJointTransversal c z) :
    IsNonramifiedJointTransversal (fun t => (c t).swap) z := by
  intro a b he hab
  simp only [edgeEquation_swap] at he ⊢
  exact ht b a he hab.symm

theorem IsNonramifiedJointTransversal.reflected {c : ℂ→Coupling} {z : ℂ}
    (ht : IsNonramifiedJointTransversal c z) :
    IsNonramifiedJointTransversal (reflectedCurve c) (star z) := by
  intro a b he hab
  have he' : edgeEquation a b (c z)=0 := by simpa [reflectedCurve] using he
  have hd := ht a b he' hab
  have heq : (fun t => edgeEquation a b (reflectedCurve c t))=
      star ∘ (fun t => edgeEquation a b (c t)) ∘ (starRingEnd ℂ) := by
    funext t
    simp [reflectedCurve]
  rw [heq,deriv_star_conj]
  simpa only [Function.comp_def,starRingEnd_apply,star_star,ne_eq,map_eq_zero] using
    (star_ne_zero.mpr hd)

theorem edgeEquation_eq_positive {K : Coupling} (hS : S K≠0) (b : ℝ) :
    edgeEquation b 1 K=S K*positiveParameter b K := by
  dsimp [edgeEquation,positiveParameter,transferC,transferB]
  field_simp
  ring

theorem edgeEquation_eq_negative {K : Coupling} (hS : S K≠0) (b : ℝ) :
    edgeEquation b (-1) K=S K*negativeParameter b K := by
  dsimp [edgeEquation,negativeParameter,transferC,transferB]
  push_cast
  field_simp
  ring

theorem IsNonramifiedJointTransversal.positive_deriv {c : ℂ→Coupling} {z : ℂ} {b : ℝ}
    (ht : IsNonramifiedJointTransversal c z) (hc : AnalyticAt ℂ c z)
    (hS : S (c z)≠0) (he : positiveParameter b (c z)=0) :
    deriv (fun t => positiveParameter b (c t)) z≠0 := by
  have hSa : AnalyticAt ℂ (fun t => S (c t)) z := curveS_analyticAt hc
  have hEa := positiveParameter_analyticAt b hc hS
  have heq : (fun t => edgeEquation b 1 (c t)) =ᶠ[𝓝 z]
      (fun t => S (c t)*positiveParameter b (c t)) := by
    filter_upwards [hSa.continuousAt.eventually_ne hS] with t ht
    exact edgeEquation_eq_positive ht b
  have he0 : edgeEquation b 1 (c z)=0 := by rw [edgeEquation_eq_positive hS b,he,mul_zero]
  have hd := ht b 1 he0 (Or.inr (Or.inr rfl))
  intro hz
  apply hd
  rw [heq.deriv_eq,(hSa.differentiableAt.hasDerivAt.fun_mul hEa.differentiableAt.hasDerivAt).deriv,he,hz]
  simp

theorem IsNonramifiedJointTransversal.negative_deriv {c : ℂ→Coupling} {z : ℂ} {b : ℝ}
    (ht : IsNonramifiedJointTransversal c z) (hc : AnalyticAt ℂ c z)
    (hS : S (c z)≠0) (he : negativeParameter b (c z)=0) :
    deriv (fun t => negativeParameter b (c t)) z≠0 := by
  have hSa : AnalyticAt ℂ (fun t => S (c t)) z := curveS_analyticAt hc
  have hEa := negativeParameter_analyticAt b hc hS
  have heq : (fun t => edgeEquation b (-1) (c t)) =ᶠ[𝓝 z]
      (fun t => S (c t)*negativeParameter b (c t)) := by
    filter_upwards [hSa.continuousAt.eventually_ne hS] with t ht
    exact edgeEquation_eq_negative ht b
  have he0 : edgeEquation b (-1) (c z)=0 := by rw [edgeEquation_eq_negative hS b,he,mul_zero]
  have hd := ht b (-1) he0 (Or.inr (Or.inl rfl))
  intro hz
  apply hd
  rw [heq.deriv_eq,(hSa.differentiableAt.hasDerivAt.fun_mul hEa.differentiableAt.hasDerivAt).deriv,he,hz]
  simp

end
end IsingBulk.Joint.Transverse
