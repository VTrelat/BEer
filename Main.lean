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

def usage : String :=
  "Usage: BEer --in <input.pog> [--out <output.smt2>] [--prelude <prelude.smt>]"

def parseArgs (args : List String) : IO (String × String × String) := do
  let mut inPath : Option String := none
  let mut outPath : Option String := none
  let mut preludePath : Option String := none
  let arr := args.toArray
  let mut i := 0
  while i < arr.size do
    let f := arr[i]!
    if f == "--in" || f == "-i" || f == "--out" || f == "-o" || f == "--prelude" || f == "-p" then
      if i + 1 < arr.size then
        let v := arr[i + 1]!
        if f == "--in" || f == "-i" then inPath := some v
        else if f == "--out" || f == "-o" then outPath := some v
        else preludePath := some v
        i := i + 2
      else throw <| IO.userError s!"{f} requires a path argument"
    else throw <| IO.userError s!"Unknown flag: {f}\n{usage}"
  let pog ← match inPath with
    | some p => pure p
    | none   => throw <| IO.userError s!"--in is required\n{usage}"
  let pogName := ((pog.splitOn "/").getLast!.splitOn ".")[0]!
  let out := outPath.getD s!"{pogName}.smt2"
  let prelude ← match preludePath with
    | some p => pure p
    | none => match ← IO.getEnv "BEER_PRELUDE" with
      | some p => pure p
      | none => pure "prelude.smt"
  return (pog, out, prelude)

def main (args : List String) : IO Unit := do
  let (pog, out, prelude) ← parseArgs args
  let pogName := ((pog.splitOn "/").getLast!.splitOn ".")[0]!
  println! s!"Reading:\t{pog}"
  let ⟨(), st⟩ ← POGtoB (← (readPOG pog).propagateError) |>.run ∅ |>.run |>.propagateError
  let ⟨(), st'⟩ ← match encode st.env |>.run ∅ with
    | .ok r => pure r
    | .error e => throw <| IO.userError s!"Error while encoding {pogName}: {e}"
  println! s!"Encoded:\t{pog}"
  let r ← match EncoderState.toSMTFile |>.run st' with
    | .ok ⟨r, _⟩ => pure r
    | .error e => throw <| IO.userError e
  saveFile (← r.addPrelude prelude) out
  println! s!"Written:\t{out}"

-- #eval MCH2POG "Test/Kumar.mch" >>= encodePOG >>= cvc5 >>= IO.println
