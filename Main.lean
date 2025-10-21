import B
import POGReader
import Encoder

open B SMT

def getPassingFiles (dataset : Nat) : IO <| List String := do
  let mut out : List String := []
  let dir : IO <| Array System.FilePath := System.FilePath.walkDir s!"/Users/vtrelat/Documents/phd-b2smt/benchmark/dataset-pog/{dataset.toPaddedString 4}"
  for path in (← dir) do
    let file ← readPOG path.toString
    match file with
    | .ok f =>
      let r ← POGtoB f |>.run ∅ |>.run
      match r with
      | .ok _ => out := out.concat ("/" ++ dataset.toPaddedString 4 ++ "/" ++ ((path.toString.splitOn "/").getLast!.splitOn ".")[0]!)
      | .error _ => continue
    | .error _ => continue
  return out

def String.addPrelude (content : String) (preludePath : String) : IO String := do
  String.append <$> IO.FS.readFile preludePath <*> pure ("\n"++content)

def saveFile (content : String) (path : String) : IO Unit := do
  IO.FS.writeFile path content

def main (args : List String) : IO Unit := do
  -- println! s!"Reading: .../dataset-pog/{pogs[45]!}.pog"
  -- let test := readPOG s!"/Users/vtrelat/Documents/phd-b2smt/benchmark/dataset-pog/{pogs[45]!}.pog"
  if h : args.length == 0 then
    println! "No path to pog provided"
    return
  else
    let pog := args[0]'(by rw [beq_iff_eq, List.length_eq_zero_iff] at h; exact List.length_pos_iff.mpr h)
    let pogName := ((pog.splitOn "/").getLast!.splitOn ".")[0]!
    println! s!"Reading:\t{pog}"
    let test := readPOG pog
    let ⟨(), st⟩ ← POGtoB (← test.propagateError) |>.run ∅ |>.run |>.propagateError
    let ⟨(), st'⟩ ← match encode (st.env) |>.run ∅ with
      | .ok r => pure r
      | .error e =>
        throw <| IO.userError s!"Error while encoding {pogName}: {e}"
    -- let ⟨(), st'⟩ ← encode (st.env) |>.run ∅ |>.propagateError
    println! s!"Encoded:\t{pog}"
    let r ← match EncoderState.toSMTFile |>.run st' with
    | .ok ⟨r, _⟩ => pure r
    | .error e => throw <| IO.userError e
    if h1 : args.length == 1 then
      saveFile (← r.addPrelude "/Users/vtrelat/Documents/phd-b2smt/lean/B/prelude.smt") s!"/Users/vtrelat/Documents/phd-b2smt/lean/B/Test/{pogName}.smt2"
    else if h2 : args.length == 2 then
      saveFile (← r.addPrelude "/Users/vtrelat/Documents/phd-b2smt/lean/B/prelude.smt") <| args[1]'(by rw [beq_iff_eq] at h2; simp [h2])
    else
      println! "Too many arguments provided"
      return

-- #eval MCH2POG "Test/Test.mch" >>= encodePOG >>= cvc5 >>= IO.println
