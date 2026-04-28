import Star.Bluespec.Lib.BluespecPrelude
import Lean
open BluespecPrelude


namespace BluespecVerification

-- Convert t_bool guard to Prop
def isReady (b : t_bool) : Prop := b = BTrue Unit_

-- Shorthands for rule transitions
def rule_fires (result : Bool × σ) : Prop := result.1 = true
def rule_state (result : Bool × σ) : σ := result.2

-- Shorthand for action method transitions
def action_state (result : t_actionvalue_ α σ) : σ := result.avAction_


attribute [bitvec_simp] bool_to_bitvec1 bit_not bit_and bit_or bitvec1_to_bool isReady rule_fires rule_state
attribute [bool_simp] bool_and bool_or bool_not
end BluespecVerification
