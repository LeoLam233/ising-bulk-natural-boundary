import IsingBulk.HT22.Transport.FieldNeighborhood.ActualFrameJets

/-! The actual finite derivative budget needed by the marked transport.
Constants precede all particle counts, radial parameters and shell points. -/
namespace IsingBulk.HT22
noncomputable section
open Set Geometry IsingBulk.Preferred22 IsingBulk.HT22.Tail
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem actual_mixed_field_finite_frame_budget (b : PreferredBranchData)
    (B : PreferredCoareaBump b) (M : ℝ) (hM : 0<M) (j : ℕ) :
    ∃ cap R ε₀ τ₀ δB : ℝ,
      0<cap ∧ cap<b.alpha ∧ 0<R ∧ 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
      ∀ N : ℕ, 0<N → ∀ ε τ μ r : ℝ,
      0<ε → ε<ε₀ → 0≤τ → τ<τ₀ → 0<r → |μ|+r+ε≤M →
      ∀ θ : Fin N → ℝ,
      (∀ i, -δB≤θ i+b.b ∧ θ i≤min cap B.delta) →
      (∀ i, μ-2*r≤θ i+b.b ∧ θ i+b.b≤μ+2*r) →
      ∀ i k : Fin N, (∀ a, θ i≤θ a ∧ θ a≤θ k) → r≤θ k-θ i →
      ∀ xs : List (Option (Fin N)), xs.length≤j → ∀ a : Fin N,
      ‖frameJet τ B.p B.m (fun t x => sourceResidual t (sourceCoordinate τ B.p B.m t x) a)
        xs (IsingBulk.Branch.radialParameter b.alpha ε) θ‖≤
        R*(N:ℝ)^(2*j+2)/(r/Real.sqrt (|μ|+r+ε))^(1+xs.length) := by
  obtain ⟨cap,C,e,t,δ,η,c,K,hcap,hcapa,hC,he,ht,hδ,hδB,hη,hc,hK,hbound⟩ :=
    actual_mixed_field_frame_jets b B M hM
  let A : ℕ → ℝ := fun m => cauchyJetConstant m*(1296*C^2/c)/η^m
  let R := 1+∑ m∈Finset.range (j+1), |A m|
  have hR : 0<R := by
    dsimp [R]
    positivity
  have hA (m : ℕ) (hm : m≤j) : A m≤R := by
    have hmem : m∈Finset.range (j+1) := Finset.mem_range.mpr (by omega)
    have hh := Finset.single_le_sum (s := Finset.range (j+1))
      (f := fun m => |A m|) (fun _ _ => abs_nonneg _) hmem
    have ha := le_abs_self (A m)
    dsimp only [R]
    linarith
  refine ⟨cap,R,e,t,δ,hcap,hcapa,hR,he,ht,hδ,hδB,?_⟩
  intro N hN ε τ μ r hε hεr hτ hτr hr hTM θ hθ hwindow i k hext hgap xs hxs a
  have hh := hbound N hN ε τ μ r hε hεr hτ hτr hr hTM θ hθ hwindow i k hext hgap xs a
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  have hT : 0< |μ|+r+ε := by positivity
  have hs : 0<Real.sqrt (|μ|+r+ε) := Real.sqrt_pos.mpr hT
  let Δ := r/Real.sqrt (|μ|+r+ε)
  have hΔ : 0<Δ := by dsimp [Δ]; positivity
  have hnump : 0≤A xs.length*(N:ℝ)^(2*xs.length+2) := by
    dsimp only [A]
    have := cauchyJetConstant_pos xs.length
    positivity
  have hnumb : A xs.length*(N:ℝ)^(2*xs.length+2)≤R*(N:ℝ)^(2*j+2) :=
    mul_le_mul (hA xs.length hxs) (pow_le_pow_right₀ hn (by omega)) (by positivity) hR.le
  have hbase : Δ≤K*r/Real.sqrt (|μ|+r+ε) := by
    calc
      _ ≤ K*Δ := le_mul_of_one_le_left hΔ.le hK
      _ = _ := by dsimp only [Δ]; ring
  have hden := pow_le_pow_left₀ hΔ.le hbase (xs.length+1)
  calc
    _ ≤ A xs.length*(N:ℝ)^(2*xs.length+2)/(K*r/Real.sqrt (|μ|+r+ε))^(xs.length+1) := hh
    _ ≤ A xs.length*(N:ℝ)^(2*xs.length+2)/Δ^(xs.length+1) :=
      div_le_div_of_nonneg_left hnump (by positivity) hden
    _ ≤ R*(N:ℝ)^(2*j+2)/Δ^(xs.length+1) :=
      div_le_div_of_nonneg_right hnumb (by positivity)
    _ = _ := by rw [Nat.add_comm 1 xs.length]

end
end IsingBulk.HT22
