import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators

/-! Announcing a requested coordinate before or after a state is sent. -/
namespace OnDemandPrecision.DemandTiming

/-- One message that answers every possible later coordinate determines the whole input. -/
theorem late_injective {I A M : Type*} (send : (I → A) → M) (read : M → I → A)
    (ok : ∀ x i, read (send x) i = x i) : Function.Injective send := by
  intro x y he
  funext i
  exact (ok x i).symm.trans ((congrArg (fun m => read m i) he).trans (ok y i))

theorem late_card {I A M : Type*} [Fintype I] [Fintype A] [Fintype M]
    (send : (I → A) → M) (read : M → I → A) (ok : ∀ x i, read (send x) i = x i) :
    Fintype.card A ^ Fintype.card I ≤ Fintype.card M := by
  classical
  simpa [Fintype.card_fun] using Fintype.card_le_of_injective send (late_injective send read ok)

/-- The transcript contains the transmitted index and its single returned value. -/
def dialogue {I A : Type*} (i : I) (x : I → A) : I × A := (i,x i)

theorem dialogue_exact {I A : Type*} (i : I) (x : I → A) : (dialogue i x).2 = x i := rfl

theorem eight_binary :
    Fintype.card (Fin 8 × Bool) = 16 ∧ Fintype.card (Fin 8 → Bool) = 256 := by
  simp

end OnDemandPrecision.DemandTiming
