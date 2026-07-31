import B
import POGReader
import Encoder
import Cli

open B SMT Cli

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

/-- Read a POG and build its `B.Env`, reporting stage timings when asked. -/
def frontend (pog : String) (timing : Bool) : IO B.Env := do
  let t0 ← IO.monoMsNow
  let xml ← (readPOG pog).propagateError
  let t1 ← IO.monoMsNow
  let ⟨(), st⟩ ← POGtoB xml |>.run ∅ |>.run |>.propagateError
  let t2 ← IO.monoMsNow
  if timing then
    IO.eprintln s!"[timing] readPOG {t1 - t0} ms"
    IO.eprintln s!"[timing] POGtoB  {t2 - t1} ms"
  return st.env

/-- Encode one environment and serialise it. -/
def backend (env : B.Env) (name : String) (timing : Bool) : IO String := do
  let t0 ← IO.monoMsNow
  let ⟨(), st⟩ ← match encode env |>.run ∅ with
    | .ok r => pure r
    | .error e => throw <| IO.userError s!"Error while encoding {name}: {e}"
  let t1 ← IO.monoMsNow
  let r ← match EncoderState.toSMTFile |>.run st with
    | .ok ⟨r, _⟩ => pure r
    | .error e => throw <| IO.userError e
  let t2 ← IO.monoMsNow
  if timing then
    IO.eprintln s!"[timing] encode    {t1 - t0} ms"
    IO.eprintln s!"[timing] toSMTFile {t2 - t1} ms"
  return r

/-- Encode each proof obligation on its own.

Every obligation is encoded against the same global environment but with
`po` restricted to that one obligation, so a file whose cost is concentrated in
a single obligation can be attributed to it.

Writes `<dir>/po_<i>.smt2`, each with the prelude prepended so it stands alone,
and reports one line per obligation on stderr.  `dir` defaults to the input's
base name, mirroring the single-file default of `<name>.smt2`; passing
`--out /dev/null` discards the files and keeps only the report. -/
def perPO (env : B.Env) (name : String) (dir : String) (prelude : String) :
    IO Unit := do
  -- `/dev/null` is the documented way to ask for timings without output, and
  -- `createDirAll` would fail on it.
  let write := dir != "/dev/null"
  if write then IO.FS.createDirAll dir
  IO.eprintln s!"[per-po] {name}: {env.po.length} proof obligations"
  for (φ, i) in env.po.zipIdx do
    let t0 ← IO.monoMsNow
    let one := { env with po := [φ] }
    match encode one |>.run ∅ with
    | .error e =>
      IO.eprintln s!"[per-po] {i}\tgoals {φ.goals.length}\tERROR {e}"
    | .ok ⟨(), st⟩ =>
      let smt := match EncoderState.toSMTFile |>.run st with
        | .ok ⟨r, _⟩ => some r
        | .error _ => none
      let ms := (← IO.monoMsNow) - t0
      let bytes := smt.map (·.length) |>.getD 0
      IO.eprintln s!"[per-po] {i}\tgoals {φ.goals.length}\thyps {φ.hyps.length}\t{ms} ms\t{bytes} B"
      if let some r := smt then
        if write then saveFile (← r.addPrelude prelude) s!"{dir}/po_{i}.smt2"
    (← IO.getStderr).flush
  if write then println! s!"Written:\t{dir}/po_<i>.smt2 ({env.po.length} files)"

/-- Encode each proof goal on its own.

Same construction as `perPO` one level down: the obligation is kept whole —
its definitions, hypotheses and local context are what the goal is proved
against — and only its `goals` list is cut to one.  The result holds a single
`check-sat`, so it is serialised flat: no `push`/`pop`, and therefore no need
for the solver's incremental mode.

Writes `<dir>/po_<i>_goal_<j>.smt2`, both indices 0-based in `.pog` order,
which is the numbering of ppTrans's `out-<i>-<j>.smt2` under `-n`; the two
tools' files pair off without a lookup table.  Each file repeats the entire
global context, so a corpus written this way is an order of magnitude larger
than the whole-file encodings — the mode is meant for streaming, emitting and
solving one script at a time.  `--out /dev/null` keeps only the report. -/
def perGoal (env : B.Env) (name : String) (dir : String) (prelude : String) :
    IO Unit := do
  let write := dir != "/dev/null"
  if write then IO.FS.createDirAll dir
  let total := env.po.foldl (· + ·.goals.length) 0
  IO.eprintln s!"[per-goal] {name}: {env.po.length} proof obligations, {total} goals"
  for (φ, i) in env.po.zipIdx do
    for (g, j) in φ.goals.zipIdx do
      let t0 ← IO.monoMsNow
      let one := { env with po := [{ φ with goals := [g] }] }
      match encode one |>.run ∅ with
      | .error e =>
        IO.eprintln s!"[per-goal] {i}\t{j}\tERROR {e}"
      | .ok ⟨(), st⟩ =>
        let smt := match EncoderState.toSMTFileFlat |>.run st with
          | .ok ⟨r, _⟩ => some r
          | .error _ => none
        let ms := (← IO.monoMsNow) - t0
        let bytes := smt.map (·.length) |>.getD 0
        IO.eprintln s!"[per-goal] {i}\t{j}\thyps {φ.hyps.length + g.hyps.length}\t{ms} ms\t{bytes} B"
        if let some r := smt then
          if write then saveFile (← r.addPrelude prelude) s!"{dir}/po_{i}_goal_{j}.smt2"
      (← IO.getStderr).flush
  if write then println! s!"Written:\t{dir}/po_<i>_goal_<j>.smt2 ({total} files)"

def runBEer (p : Parsed) : IO UInt32 := do
  let pog := p.positionalArg! "input" |>.as! String
  let pogName := ((pog.splitOn "/").getLast!.splitOn ".")[0]!
  let prelude ← match p.flag? "prelude" |>.map (·.as! String) with
    | some q => pure q
    | none => pure <| (← IO.getEnv "BEER_PRELUDE").getD "prelude.smt"
  let timing := p.hasFlag "timing"
  let out := p.flag? "out" |>.map (·.as! String)
  let env ← frontend pog timing
  if p.hasFlag "per-goal" then
    perGoal env pogName (out.getD pogName) prelude
    return 0
  if p.hasFlag "per-po" then
    perPO env pogName (out.getD pogName) prelude
    return 0
  println! s!"Reading:\t{pog}"
  let r ← backend env pogName timing
  println! s!"Encoded:\t{pog}"
  let outPath := out.getD s!"{pogName}.smt2"
  saveFile (← r.addPrelude prelude) outPath
  println! s!"Written:\t{outPath}"
  return 0

def beerCmd : Cmd := `[Cli|
  BEer VIA runBEer; ["0.1.0"]
  "Translate an Atelier B proof-obligation file (.pog) to SMT-LIB."

  FLAGS:
    o, out : String;     "Output file (default <input>.smt2). With --per-po or --per-goal, a \
                          directory receiving one file per obligation resp. goal (default \
                          <input>/). /dev/null discards."
    p, prelude : String; "SMT-LIB preamble to prepend (default: $BEER_PRELUDE or ./prelude.smt)."
    "per-po";            "Encode each proof obligation separately, reporting its cost on stderr."
    "per-goal";          "Encode each proof goal separately, as po_<i>_goal_<j>.smt2 — both \
                          indices 0-based in .pog order, so the files pair off with ppTrans -n's \
                          out-<i>-<j>.smt2. One (check-sat) per file and no push/pop, so cvc5 \
                          needs no --incremental. Every file repeats the whole global context and \
                          the set is far larger than the whole-file encoding: stream it, do not \
                          keep it. Takes precedence over --per-po."
    timing;              "Report per-stage timings (readPOG, POGtoB, encode, toSMTFile) on stderr."

  ARGS:
    input : String;      "The .pog file to translate."
]

def main (args : List String) : IO UInt32 := do
  -- `--in`/`-i` used to be the way to name the input; keep it working.
  let args := args.flatMap fun a => if a == "--in" || a == "-i" then [] else [a]
  beerCmd.validate args
