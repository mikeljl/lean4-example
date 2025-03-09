import Mathlib.Algebra.Group.Defs  -- Import algebra group definitions
import hello
open Nat (add_assoc add_comm)

theorem hello_world (a b c : Nat)
  : a + b + c = a + c + b := by
  rw [add_assoc, add_comm b, ←add_assoc]

theorem foo (a : Nat) : a + 1 = Nat.succ a := by rfl

variable {G : Type*} [Group G]

theorem inv_mul_self' (a : G) : a⁻¹ * a = 1 := inv_mul_cancel a
