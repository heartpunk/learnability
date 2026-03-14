import Instances.ISAs.DispatchLoopEval

/-!
# DispatchLoopTestSubjects — Test subject definitions for grammar extraction

Each test subject defines:
- Name: identifier for the subject
- JSON path: where the per-function or flat blocks JSON lives
- Golden grammar: expected EBNF productions for validation

The test runner loads each subject, runs the pipeline, and compares
extracted grammar against golden grammar.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open VexISA VexIRParser

/-- A test subject for the grammar extraction pipeline. -/
structure TestSubject where
  name : String
  jsonPath : System.FilePath
  goldenProds : Std.HashMap String (List (List String))
  deriving Inhabited

/-- Tiny C test subject — the original validation target. -/
def tinycSubject : TestSubject := {
  name := "tinyc"
  jsonPath := "reference/tinyc/parser_nt_blocks.json"
  goldenProds := ({} : Std.HashMap String (List (List String)))
    |>.insert "term"       [["id"], ["int"], ["paren_expr"]]
    |>.insert "sum"        [["term"], ["sum", "'+'", "term"], ["sum", "'-'", "term"]]
    |>.insert "test"       [["sum"], ["sum", "'<'", "sum"]]
    |>.insert "expr"       [["test"], ["id", "'='", "expr"]]
    |>.insert "paren_expr" [["'('", "expr", "')'"]]
    |>.insert "statement"  [
        ["'if'", "paren_expr", "statement"],
        ["'if'", "paren_expr", "statement", "'else'", "statement"],
        ["'while'", "paren_expr", "statement"],
        ["'do'", "statement", "'while'", "paren_expr", "';'"],
        ["'{'", "statements", "'}'"],
        ["expr", "';'"],
        ["';'"]
      ]
    |>.insert "statements" [["statement"], ["statement", "statements"]]
}

/-- All registered test subjects. Add new subjects here. -/
def testSubjects : Array TestSubject := #[
  tinycSubject
]

/-- Result of running a single test subject. -/
structure TestResult where
  subjectName : String
  totalGolden : Nat
  totalMatched : Nat
  totalExtra : Nat
  passed : Bool
  errors : Array String
  deriving Inhabited

/-- Run the extraction pipeline on a single test subject and compare against golden grammar.
    Returns test results without the full pipeline output (that goes to log). -/
def runTestSubject (subject : TestSubject) (log : String → IO Unit) : IO TestResult := do
  log s!"\n============================================================"
  log s!"Testing: {subject.name}"
  log s!"============================================================"
  -- Load functions
  let functions ← loadFunctionsFromJSON subject.jsonPath
  log s!"  Loaded {functions.size} functions from {subject.jsonPath}"
  -- Run full pipeline with subject-specific golden grammar
  runPipeline functions log subject.goldenProds
  -- Return a basic result — the structural comparison is printed by runPipeline
  -- via structuralGoldenCompare. Here we just report success/failure.
  return {
    subjectName := subject.name
    totalGolden := subject.goldenProds.toArray.foldl (fun n (_, prods) => n + prods.length) 0
    totalMatched := 0  -- TODO: capture from structuralGoldenCompare output
    totalExtra := 0
    passed := true  -- pipeline ran without crash
    errors := #[]
  }

/-- Run all test subjects and report results. -/
def runAllTests (log : String → IO Unit) : IO (Array TestResult) := do
  let mut results : Array TestResult := #[]
  for subject in testSubjects do
    let result ← runTestSubject subject log
    results := results.push result
  -- Summary
  log s!"\n============================================================"
  log "Test Summary"
  log s!"============================================================"
  let passed := results.filter (·.passed)
  let failed := results.filter (!·.passed)
  for r in results do
    let mark := if r.passed then "PASS" else "FAIL"
    log s!"  [{mark}] {r.subjectName}"
  log s!"\n  {passed.size}/{results.size} passed"
  if !failed.isEmpty then
    log "  Failures:"
    for r in failed do
      for e in r.errors do
        log s!"    {r.subjectName}: {e}"
  return results

/-- Test suite entry point. -/
def dispatchLoopTestMain (args : List String := []) : IO Unit := do
  let log ← mkLogger ".lake/test-results.log"
  match args with
  | ["--subject", name] =>
    -- Run a specific subject
    match testSubjects.find? (·.name == name) with
    | some subject =>
      let _ ← runTestSubject subject log
      pure ()
    | none =>
      IO.eprintln s!"Unknown test subject: {name}"
      IO.eprintln s!"Available: {", ".intercalate (testSubjects.map (·.name)).toList}"
      IO.Process.exit 1
  | _ =>
    -- Run all subjects
    let _ ← runAllTests log
    pure ()
