import IsingBulk.Preferred22.FrameProduct
import IsingBulk.Preferred22.RegularFrameJets

/-! Exact normalizer-preserving seed bounds from the actual real cell
weight and individual regular one-body factors. -/
namespace IsingBulk.Preferred22
noncomputable section
open Filter Set
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

theorem preferredFrameJet_const_mul {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (F : ℂ → (Fin N → ℝ) → ℂ)
    (hF : PreferredMixedSmoothOn (fun z => F z.1 z.2) Ω)
    (c : ℂ) (xs : List (Option (Fin N))) (s : ℂ) (θ : Fin N → ℝ) (hz : (s,θ)∈Ω) :
    preferredFrameJet τ p m (fun t x => c*F t x) xs s θ=
      c*preferredFrameJet τ p m F xs s θ := by
  induction xs generalizing s θ with
  | nil => rfl
  | cons a xs ih =>
    have hmixed := preferredFrameJet_mixed τ δ p m hp hm Ω hΩ hpoint F hF xs
    rw [preferredFrameJet_cons]
    rw [preferredFrameStep_congr_open τ p m a _
      (fun t x => c*preferredFrameJet τ p m F xs t x) Ω hΩ (fun z hz => ih z.1 z.2 hz) s θ hz]
    rw [preferredFrameStep_mul τ p m a (fun _ _ => c) _ s θ
      (differentiableAt_const c) (hmixed (s,θ) hz).2
      (fun _ => differentiableAt_const c)
      (preferredMixed_coordinate_differentiable _ s θ (hmixed (s,θ) hz).1)]
    rw [preferredFrameStep_const]
    simp only [zero_mul,zero_add,preferredFrameJet_cons]

theorem preferred_seed_normalizer_ne_zero (N : ℕ) :
    (N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1)≠0 := by
  apply mul_ne_zero
  · exact_mod_cast Nat.factorial_ne_zero N
  · apply pow_ne_zero
    exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)

/-- All normalized seed frame derivatives inherit only an exponential
factor and a fixed particle-count polynomial. The factorial stays exact. -/
theorem preferred_source_seed_frame_bound {N : ℕ} (hN : 0<N)
    (τ δ : ℝ) (η p m r : ℝ → ℝ)
    (hη : ContDiff ℝ ∞ η) (hp : ContDiff ℝ ∞ p)
    (hm : ContDiff ℝ ∞ m) (hr : ContDiff ℝ ∞ r)
    (s : ℂ) (θ : Fin N → ℝ) (hpoint : PreferredFramePoint τ δ p m s θ)
    (hθ : ∀ i, θ i∈Ioo (-Real.pi-δ) δ)
    (j L : ℕ) (Cw Ca : ℝ) (hCw : 1≤Cw) (hCa : 1≤Ca)
    (hwbound : ∀ xs : List (Option (Fin N)), xs.length≤j →
      ‖preferredFrameJet τ p m (fun _ x => (preferredCellWeight .right η p m r x:ℂ)) xs s θ‖≤
        Cw^N*(N:ℝ)^L)
    (habound : ∀ i (xs : List (Option (Fin N))), xs.length≤j →
      ‖preferredFrameJet τ p m
        (fun t x => preferredRegularOneBody t (preferredSourceCoordinate τ p m t x i)) xs s θ‖≤Ca)
    (xs : List (Option (Fin N))) (hxs : xs.length≤j) :
    ‖((N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1))*
      preferredFrameJet τ p m (preferredRegularSeedCoefficient τ η p m r) xs s θ‖≤
        (2^j*Cw*(2^j*Ca))^N*(N:ℝ)^L := by
  have hgeom := preferredFramePoint_eventually τ δ p m hp hm s θ hpoint hθ
  obtain ⟨Ω,hΩsub,hΩ,hz⟩ := mem_nhds_iff.mp hgeom
  have hΩpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2 := fun z hz => hΩsub hz
  have hseed := preferredRegularSeedCoefficient_mixed τ δ η p m r hη hp hm hr Ω hΩpoint
  have hbody := (preferred_regular_factors_mixed τ δ p m hp hm Ω hΩpoint).2
  have hw : ContDiff ℝ ∞ (fun x : Fin N → ℝ => preferredCellWeight .right η p m r x) := by
    unfold preferredCellWeight preferredLowerWeight preferredRightWeight lowerWeight occupancy
    fun_prop
  have hwm : PreferredMixedSmoothOn (fun z : ℂ × (Fin N → ℝ) =>
      (preferredCellWeight .right η p m r z.2:ℂ)) Ω := by
    intro z _
    exact ⟨(Complex.ofRealCLM.contDiff.comp (hw.comp contDiff_snd)).contDiffAt,
      differentiableAt_const (𝕜:=ℂ) (x:=z.1) (preferredCellWeight .right η p m r z.2:ℂ)⟩
  have hprod : PreferredMixedSmoothOn (fun z : ℂ × (Fin N → ℝ) =>
      ∏ i, preferredRegularOneBody z.1 (preferredSourceCoordinate τ p m z.1 z.2 i)) Ω := by
    intro z hz
    exact ⟨contDiffAt_prod (fun i _ => (hbody i z hz).1),
      DifferentiableAt.fun_finsetProd (fun i _ => (hbody i z hz).2)⟩
  have hCa0 : 0≤Ca := le_trans (by norm_num) hCa
  have hCw0 : 0≤Cw := le_trans (by norm_num) hCw
  have hpb (ys : List (Option (Fin N))) (hys : ys.length≤j) :
      ‖preferredFrameJet τ p m (fun t x =>
        ∏ i, preferredRegularOneBody t (preferredSourceCoordinate τ p m t x i)) ys s θ‖≤(2^j*Ca)^N := by
    simpa only [Finset.prod_map_toList,Finset.length_toList,Finset.card_univ,Fintype.card_fin] using
      preferredFrameJet_list_prod_bound τ δ p m hp hm Ω hΩ hΩpoint
        (fun i t x => preferredRegularOneBody t (preferredSourceCoordinate τ p m t x i))
        (Finset.univ.toList : List (Fin N)) (fun i _ => hbody i) s θ hz j Ca hCa0
        (fun i _ => habound i) ys hys
  let Z : ℂ := (N.factorial:ℂ)*(2*Real.pi:ℂ)^(N-1)
  have he : (fun (t : ℂ) (x : Fin N → ℝ) => Z*preferredRegularSeedCoefficient τ η p m r t x)=
      (fun t x => (preferredCellWeight .right η p m r x:ℂ)*
        ∏ i, preferredRegularOneBody t (preferredSourceCoordinate τ p m t x i)) := by
    funext t x
    change Z*((preferredCellWeight .right η p m r x:ℂ)*
      (∏ i, preferredRegularOneBody t (preferredSourceCoordinate τ p m t x i))/Z)=_
    rw [←mul_div_assoc]
    apply (div_eq_iff (preferred_seed_normalizer_ne_zero N)).2
    ring
  change ‖Z*preferredFrameJet τ p m (preferredRegularSeedCoefficient τ η p m r) xs s θ‖≤_
  rw [←preferredFrameJet_const_mul τ δ p m hp hm Ω hΩ hΩpoint
    (preferredRegularSeedCoefficient τ η p m r) hseed Z xs s θ hz,he]
  have hh := preferredFrameJet_mul_bound τ δ p m hp hm Ω hΩ hΩpoint
    (fun _ x => (preferredCellWeight .right η p m r x:ℂ))
    (fun t x => ∏ i, preferredRegularOneBody t (preferredSourceCoordinate τ p m t x i))
    hwm hprod s θ hz j (Cw^N*(N:ℝ)^L) ((2^j*Ca)^N) (by positivity) (by positivity)
    hwbound hpb xs hxs
  apply hh.trans
  have htwo : (2:ℝ)^j≤((2:ℝ)^j)^N := by
    simpa only [pow_one] using pow_le_pow_right₀ (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
      (Nat.succ_le_iff.mpr hN)
  calc
    _ ≤ ((2:ℝ)^j)^N*(Cw^N*(N:ℝ)^L)*((2:ℝ)^j*Ca)^N := by
      gcongr
    _ = _ := by rw [mul_pow,mul_pow]; ring

end
end IsingBulk.Preferred22
