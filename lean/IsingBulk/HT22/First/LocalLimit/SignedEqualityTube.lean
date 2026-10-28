import IsingBulk.HT22.First.LocalLimit.SignedMeanGap
import IsingBulk.Preferred22.FiniteEqualityGeometry

namespace IsingBulk.HT22.LocalLimit
noncomputable section
open IsingBulk.PrimeFamily Arithmetic IsingBulk.Preferred22
open scoped BigOperators

/-- Actual affine signed equality means, including all collision points,
are separated from the branch on a whole fixed finite-order tube. -/
theorem finite_signed_equality_tube {p : ℕ} (hp : p.Prime) (hp5 : 5≤p)
    {a : ℤ} (ha : PrimeIndex p a) {M : ℕ} (hM : 0<M) :
    let b := Real.arccos (|2*Real.cos (angle p a)|-1)
    ∃ g : ℝ, 0<g ∧ ∀ negative : Bool, ∀ N : ℕ, 0<N → N≤M →
      ∀ δ : ℝ, δ≤g/4 → ∀ l : ℤ, ∀ w : Fin N → ℝ,
      (∑ i,w i)=2*Real.pi*l+Physical.constraintAngle negative →
      (∀ i,-δ≤w i+b) → preferredAngularDiameter w≤g/4 →
      (∀ i,|w i-signedEqualityMean negative N l|≤preferredAngularDiameter w) ∧
      (∀ i,g/2≤w i+b) := by
  dsimp only
  let b := Real.arccos (|2*Real.cos (angle p a)|-1)
  obtain ⟨g,hg,hsep⟩ := finite_signed_mean_separation hp hp5 ha hM
  refine ⟨g,hg,?_⟩
  intro negative N hN hNM δ hδ l w hsum hbox hD
  have hNr : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
  have ht : (∑ i,w i)=(N:ℝ)*signedEqualityMean negative N l := by
    rw [hsum,signedEqualityMean,mul_div_cancel₀ _ hNr]
  have hwindow := preferred_mean_diameter_window hN w (signedEqualityMean negative N l) ht
  have hgap := hsep negative N (by omega) hNM l
  have htpos : g≤b+signedEqualityMean negative N l := by
    rcases le_abs.mp hgap with h | h
    · exact h
    · let i : Fin N := ⟨0,hN⟩
      have hi := (abs_le.mp (hwindow i)).2
      have hb := hbox i
      dsimp only [b] at *
      linarith
  refine ⟨hwindow,?_⟩
  intro i
  have hi := (abs_le.mp (hwindow i)).1
  linarith

end
end IsingBulk.HT22.LocalLimit
