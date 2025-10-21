import POGReader
import Encoder

open Lean Elab Command Term Meta

syntax (name := beer) "#beer" (atomic("(" &"verbose" ")"))? str : command

def beerImpl_aux (file : String) (verbose := false) : CommandElabM Unit := do
  let filepath ← MCH2POG file
  let pog ← encodePOG filepath
  let output ← cvc5 pog
  logInfo s!"🍺 Cheers! 🍺\n{output}"
  if verbose then logInfo s!"🍻 Encoding 🍻\n{pog}"

@[command_elab beer]
def beerImpl : CommandElab := fun
  | `(#beer $file:str) => do
    beerImpl_aux file.getString
  | `(#beer (verbose) $file:str) => do
    beerImpl_aux file.getString true
  | _ => throwUnsupportedSyntax

-- #beer (verbose) "Test/Test.mch"
