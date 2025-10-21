import Lean.Elab.Term
import Lean.Data.Options

elab "get_option%" flag:name : term => do
  let opts ← Lean.MonadOptions.getOptions
  let flagName := flag.getName

  match opts.find flagName <|> (← Lean.getOptionDefaultValue flagName) with
  | none => unreachable!
  | some (.ofString s) => return .lit <| .strVal s
  | some (.ofBool b) => return .const (bif b then `Bool.true else `Bool.false) []
  | some (.ofNat n) => return .lit <| .natVal n
  | some v => throwError s!"Unimplemented get_option for {v}"

register_option termColors : Bool := { defValue := false }
