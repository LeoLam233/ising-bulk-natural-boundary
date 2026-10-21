import IsingBulk.HT.Tail.SignedMixedKernelTransport
import IsingBulk.Tail.MixedActualDensityBound

/-! Exact all-order transfer of the mixed source to a unit-signed global
kernel. Only the nonzero global kernel is cancelled; complete pair factors
and their collision zeros are never divided out. -/
namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail IsingBulk.Lie IsingBulk.HT.Contour Set Filter
open scoped Topology ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem parameterSmooth_iterate_mul_frozen_germ {n : ℕ} {Ω : Set (ℂ × AngularSpace n)}
    (hΩ : IsOpen Ω) (V : ℂ → AngularSpace n → Fin (n+1) → ℂ)
    (K A : ℂ → AngularSpace n → ℂ)
    (hV : ∀ i, ParameterSmoothOn Ω (fun s x => V s x i))
    (hK : ParameterSmoothOn Ω K) (hA : ParameterSmoothOn Ω A)
    {p : ℂ × AngularSpace n} (hp : p ∈ Ω)
    (hfreeze : ∀ᶠ q in 𝓝 p, transport V K q.1 q.2 = 0) (k : ℕ) :
    Function.uncurry ((lieStep V)^[k] (fun s x => K s x*A s x)) =ᶠ[𝓝 p]
      Function.uncurry (fun s x => K s x*((lieStep V)^[k] A) s x) := by
  induction k with
  | zero => exact Eventually.of_forall (fun _ => rfl)
  | succ k ih =>
    have he := lieStep_joint_germ V p.1 p.2 ih
    have hAk := hA.iterate_lieStep hΩ V A hV k
    filter_upwards [he,hΩ.mem_nhds hp,hfreeze] with q hq hqΩ hqf
    dsimp only [Function.uncurry] at hq ⊢
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply',hq]
    exact lieStep_mul_frozen V K _ q.1 q.2 (hK q hqΩ).2 (hAk q hqΩ).2
      (hK.angular_differentiableAt hqΩ) (hAk.angular_differentiableAt hqΩ)
      (fun i => (hV i).angular_differentiableAt hqΩ) hqf

theorem signed_mixed_kernel_all_order (σ : ℂ) (hσ : ‖σ‖ = 1) {n : ℕ}
    (J : Finset (Fin (n+1))) (j q : Fin (n+1)) (hj : j ∈ J)
    (f : SelectorFunctions) {r : ℝ} (hr : 0 < r) (τ lam : ℝ)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hY : ∀ x : Fin (n+1) → ℝ, ‖coordinateProduct (deformedPoint f r τ lam x)‖ < 1)
    (w : AngularSpace n → ℂ) (hw : ContDiff ℝ ∞ w)
    (s : ℂ) (θ : AngularSpace n) (hΩ : (s,θ) ∈ mixedSeparatedDomain J j q f r τ lam)
    (hpg : ∀ i ∈ insert q J, f.p =ᶠ[𝓝 (θ i)] (fun _ => f.p (θ i)))
    (hmg : ∀ i ∈ insert q J, f.m =ᶠ[𝓝 (θ i)] (fun _ => f.m (θ i))) (k : ℕ) :
    ((lieStep (mixedContourVelocity J j q f r τ lam))^[k]
      (fun z x => w x*signedPulledDensity σ f r τ lam z x)) s θ =
      signedMixedSimpleKernel σ f r τ lam s θ*
        ((lieStep (mixedContourVelocity J j q f r τ lam))^[k]
          (fun z x => w x*compactRegularDensity f r τ lam z x)) s θ := by
  let Ω := mixedSeparatedDomain J j q f r τ lam
  let V := mixedContourVelocity J j q f r τ lam
  have hopen := mixedSeparatedDomain_isOpen J j q f hr τ lam hp hm
  have hV := fun i => mixedSeparated_velocity_smooth J j q f hr τ lam hp hm i
  have hK := signed_mixedSeparated_kernel_smooth σ hσ (Nat.succ_pos n) J j q f hr τ lam hp hm hY
  have hA := (ParameterSmoothOn.angular Ω w hw).mul
    (mixedSeparated_regularDensity_smooth (Nat.succ_pos n) J j q f hr τ lam hp hm)
  have hplateau : ∀ᶠ p : ℂ × AngularSpace n in 𝓝 (s,θ),
      ∀ i ∈ insert q J, deriv f.p (p.2 i)=0 ∧ deriv f.m (p.2 i)=0 := by
    apply (Filter.eventually_all_finset (insert q J)).mpr
    intro i hi
    have hcoord : Continuous (fun p : ℂ × AngularSpace n => p.2 i) :=
      (continuous_apply i).comp continuous_snd
    have hcoordAt : ContinuousAt (fun p : ℂ × AngularSpace n => p.2 i) (s, θ) :=
      hcoord.continuousAt
    have hpd := hcoordAt.tendsto.eventually (hpg i hi).deriv
    have hmd := hcoordAt.tendsto.eventually (hmg i hi).deriv
    filter_upwards [hpd,hmd] with p hp' hm'
    simpa only [deriv_const] using And.intro hp' hm'
  have hfreeze : ∀ᶠ p : ℂ × AngularSpace n in 𝓝 (s,θ),
      transport V (signedMixedSimpleKernel σ f r τ lam) p.1 p.2 = 0 := by
    filter_upwards [hopen.mem_nhds hΩ,hplateau] with p hpΩ hpl
    exact signed_mixed_actual_kernel_frozen σ hσ J j q f hr τ lam p.1 p.2 hj hp hm
      (fun i hi => hpl i (by rcases hi with hi | hi; exact Finset.mem_insert_of_mem hi; simp [hi])) hpΩ hY
  have he : (fun z x => w x*signedPulledDensity σ f r τ lam z x)=
      (fun z x => signedMixedSimpleKernel σ f r τ lam z x*(w x*compactRegularDensity f r τ lam z x)) := by
    funext z x
    rw [signed_compact_pulledDensity_factorization]
    ring
  rw [he]
  exact (parameterSmooth_iterate_mul_frozen_germ hopen V _ _ hV hK hA hΩ hfreeze k).eq_of_nhds

/-- The true signed Lie iterate inherits the already proved complete
Gaussian numerator bound. Its poles remain the actual signed poles. -/
theorem signed_mixed_iterate_norm_transfer (σ : ℂ) (hσ : ‖σ‖ = 1) {n : ℕ}
    (J : Finset (Fin (n+1))) (j q : Fin (n+1)) (hj : j ∈ J)
    (f : SelectorFunctions) {r : ℝ} (hr : 0 < r) (τ lam : ℝ)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hY : ∀ x : Fin (n+1) → ℝ, ‖coordinateProduct (deformedPoint f r τ lam x)‖ < 1)
    (w : AngularSpace n → ℂ) (hw : ContDiff ℝ ∞ w)
    (s : ℂ) (θ : AngularSpace n) (hΩ : (s,θ) ∈ mixedSeparatedDomain J j q f r τ lam)
    (hpg : ∀ i ∈ insert q J, f.p =ᶠ[𝓝 (θ i)] (fun _ => f.p (θ i)))
    (hmg : ∀ i ∈ insert q J, f.m =ᶠ[𝓝 (θ i)] (fun _ => f.m (θ i))) (k : ℕ)
    {B : ℝ} (hbound : ‖((lieStep (mixedContourVelocity J j q f r τ lam))^[k]
      (fun z x => w x*pulledDensity f r τ lam z x)) s θ‖ ≤ B*‖mixedSimpleKernel f r τ lam s θ‖) :
    ‖((lieStep (mixedContourVelocity J j q f r τ lam))^[k]
      (fun z x => w x*signedPulledDensity σ f r τ lam z x)) s θ‖ ≤ B*‖signedMixedSimpleKernel σ f r τ lam s θ‖ := by
  have hSigned := signed_mixed_kernel_all_order σ hσ J j q hj f hr τ lam hp hm hY w hw s θ hΩ hpg hmg k
  have hOriginal := signed_mixed_kernel_all_order (1:ℂ) (by simp) J j q hj f hr τ lam hp hm hY w hw s θ hΩ hpg hmg k
  have hD1 : signedPulledDensity (N := n+1) (1:ℂ) f r τ lam =
      pulledDensity (N := n+1) f r τ lam := by
    funext z x
    exact signedPulledDensity_one f r τ lam z x
  have hK1 : signedMixedSimpleKernel (N := n+1) (1:ℂ) f r τ lam =
      mixedSimpleKernel (N := n+1) f r τ lam := by
    funext z x
    simp only [signedMixedSimpleKernel,mixedSimpleKernel,one_mul]
  rw [hD1,hK1] at hOriginal
  rw [hOriginal,norm_mul] at hbound
  have hKpos : 0 < ‖mixedSimpleKernel f r τ lam s θ‖ := norm_pos_iff.mpr (by
    unfold mixedSimpleKernel
    exact mul_ne_zero (inv_ne_zero (one_sub_coordinateProduct_ne_zero (Nat.succ_pos n)
      (fun i => interiorRoot_norm_lt_one (hΩ.2.1 i)))) (inv_ne_zero hΩ.2.2.2.2))
  have hReg : ‖((lieStep (mixedContourVelocity J j q f r τ lam))^[k]
      (fun z x => w x*compactRegularDensity f r τ lam z x)) s θ‖ ≤ B :=
    (mul_le_mul_iff_right₀ hKpos).mp (hbound.trans_eq (mul_comm _ _))
  rw [hSigned,norm_mul]
  exact (mul_le_mul_of_nonneg_left hReg (norm_nonneg _)).trans_eq (mul_comm _ _)

end
end IsingBulk.HT.Tail
