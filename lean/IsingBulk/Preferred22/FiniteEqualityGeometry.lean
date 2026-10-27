import IsingBulk.Preferred22.FiniteMeanSeparation
import IsingBulk.Preferred22.ShellCover
import IsingBulk.Preferred22.CoordinateDiameter

/-! Literal small-diameter source geometry, including full equality itself.
The finite prime-branch gap places the entire tube in a fixed regular arc. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set
open scoped BigOperators

theorem preferred_mean_diameter_window {N : ℕ} (hN : 0<N)
    (w : Fin N → ℝ) (t : ℝ) (hmean : (∑i,w i)=(N:ℝ)*t) :
    ∀i,|w i-t|≤preferredAngularDiameter w := by
  have hNr : 0<(N:ℝ) := by exact_mod_cast hN
  intro i
  have hpair (v : Fin N) := abs_le.mp (preferredAngularDiameter_pair_le w v i)
  have hlo := Finset.sum_le_sum (s:=Finset.univ)
    (f:=fun _ : Fin N => w i-preferredAngularDiameter w) (g:=w)
    (fun v _ => by linarith [(hpair v).1])
  have hup := Finset.sum_le_sum (s:=Finset.univ)
    (f:=w) (g:=fun _ : Fin N => w i+preferredAngularDiameter w)
    (fun v _ => by linarith [(hpair v).2])
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,hmean] at hlo hup
  rw [abs_le]
  constructor <;> nlinarith

/-- Every point in the actual finite equality tube, including its center,
is a uniformly regular distance from the physical inverse branch. -/
theorem preferred_finite_equality_tube_geometry (d : PreferredBranchData)
    {p : ℕ} (hp : p.Prime) {a : ℤ} (ha : IsingBulk.PrimeFamily.Admissible p a)
    (hα : d.alpha=IsingBulk.PrimeFamily.angle p a) {M : ℕ} (hM : 0<M) :
    ∃g : ℝ,0<g ∧ ∀B : PreferredCoareaBump d,∀n : ℕ,n+1≤M→
      ∀δB : ℝ,δB≤g/4→∀θ : Fin n → ℝ,θ∈preferredRightRegion d B δB→
      preferredAngularDiameter (preferredLiftedAngles B.delta (constrainedAngles θ))≤g/4→
      ∃l : ℤ,
        (∑i,preferredLiftedAngles B.delta (constrainedAngles θ) i)=2*Real.pi*(l:ℝ) ∧
        IsingBulk.PrimeFamily.angle (n+1) l∈Icc (-d.b+g) B.delta ∧
        (∀i,|preferredLiftedAngles B.delta (constrainedAngles θ) i-
          IsingBulk.PrimeFamily.angle (n+1) l|≤
            preferredAngularDiameter (preferredLiftedAngles B.delta (constrainedAngles θ))) ∧
        (∀i,g/2≤preferredLiftedAngles B.delta (constrainedAngles θ) i+d.b) := by
  obtain ⟨g,hg,hgap⟩ := preferred_finite_mean_separation d hp ha hα hM
  refine ⟨g,hg,?_⟩
  intro B n hNM δB hδB θ hθ hD
  obtain ⟨l,hl⟩ := preferredLiftedAngles_integer_mean B.delta θ
  let w := preferredLiftedAngles B.delta (constrainedAngles θ)
  let t := IsingBulk.PrimeFamily.angle (n+1) l
  have hNr : 0<((n+1:ℕ):ℝ) := by positivity
  have ht : (∑i,w i)=((n+1:ℕ):ℝ)*t := by
    dsimp [t,IsingBulk.PrimeFamily.angle]
    rw [mul_div_cancel₀ _ (ne_of_gt hNr)]
    exact hl
  have hwindow := preferred_mean_diameter_window (by omega : 0<n+1) w t ht
  have hu0 := (hθ.2 (0:Fin (n+1))).1
  have hw0 := (abs_le.mp (hwindow 0)).2
  have hgap' : g≤|d.b+t| := by
    simpa only [preferredShellMean,IsingBulk.PrimeFamily.angle,t] using hgap (n+1) (by omega) hNM l
  have htpos : g≤d.b+t := by
    rcases le_abs.mp hgap' with h | h
    · exact h
    · change -d.b-δB≤w 0 at hu0
      change preferredAngularDiameter w≤g/4 at hD
      linarith
  have htu : t≤B.delta := by
    have hh := Finset.sum_le_sum (s:=Finset.univ) (f:=w)
      (g:=fun _ : Fin (n+1) => B.delta) (fun i _ => (hθ.2 i).2)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,ht] at hh
    exact (mul_le_mul_iff_right₀ hNr).mp (by simpa only [mul_comm] using hh)
  refine ⟨l,hl,⟨by dsimp [t] at htpos; linarith,htu⟩,hwindow,?_⟩
  intro i
  have hi := (abs_le.mp (hwindow i)).1
  change preferredAngularDiameter w≤g/4 at hD
  change g/2≤w i+d.b
  linarith

end
end IsingBulk.Preferred22
