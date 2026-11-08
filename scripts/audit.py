#!/usr/bin/env python3
"""Check source controls and collect transitive axioms from the Lean environment."""

import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = re.compile(r"\b(sorry|admit|axiom|sorryAx|unsafe|native_decide)\b")


def code_only(text):
    """Remove nested comments and strings without joining surrounding tokens."""
    result = []
    i = depth = 0
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                i += 1
        elif text.startswith("/-", i):
            result.append(" ")
            depth = 1
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end == -1 else end
        elif text[i] == '"':
            result.append(" ")
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
        else:
            result.append(text[i])
            i += 1
    assert depth == 0, "Unclosed block comment"
    return "".join(result)


def main():
    for word in ["sorry", "admit", "axiom", "sorryAx", "unsafe", "native_decide"]:
        assert FORBIDDEN.search(code_only(f"theorem bad : False := by {word}"))
    assert not FORBIDDEN.search(code_only('/- sorry /- axiom -/ admit -/ def s := "unsafe"'))
    sources = [ROOT / "SupercriticalLogRank.lean", ROOT / "Solution.lean"]
    sources += sorted((ROOT / "SupercriticalLogRank").glob("*.lean"))
    for path in sources + [ROOT / "Challenge.lean"]:
        assert not path.is_symlink(), path
        text = path.read_text()
        code = code_only(text)
        assert code.lstrip().startswith("module"), path
        assert len(text.splitlines()) <= 10000, path
        if path.name != "Challenge.lean":
            assert not FORBIDDEN.search(code), path
    challenge = ROOT / "Challenge.lean"
    assert len(challenge.read_bytes()) <= 100 * 1024
    assert len(challenge.read_text().splitlines()) <= 1000
    assert len(re.findall(r"\bsorry\b", code_only(challenge.read_text()))) == 3
    probe = '''import Solution
import Lean.Util.CollectAxioms
open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if name.toString.startsWith "SupercriticalLogRank." ||
        name.toString.startsWith "ConditionalLogRank." then
      let axioms ← collectAxioms name
      let record := toJson (name.toString, axioms.map Name.toString)
      logInfo m!"AUDIT_RECORD {record.compress}"
      count := count + 1
  logInfo m!"AUDIT_COUNT {count}"
'''
    with tempfile.TemporaryDirectory(prefix="conditional-rank-audit-") as folder:
        path = Path(folder) / "Audit.lean"
        path.write_text(probe)
        result = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                                capture_output=True, text=True)
    log = result.stdout + result.stderr
    (ROOT / "audit/local-axioms.log").write_text(log)
    assert result.returncode == 0, log
    records = [json.loads(line.split("AUDIT_RECORD ", 1)[1])
               for line in log.splitlines() if "AUDIT_RECORD " in line]
    count = re.search(r"AUDIT_COUNT (\d+)", log)
    assert count and int(count[1]) == len(records) and len(records) > 0
    records = dict(records)
    names = json.loads((ROOT / "comparator.json").read_text())["theorem_names"]
    assert all(name in records for name in names)
    for name, axioms in records.items():
        assert set(axioms) <= ALLOWED, (name, axioms)
    report = {
        "status": "pass", "declarations": len(records),
        "axioms": sorted({a for axioms in records.values() for a in axioms}),
        "selected": {name: records[name] for name in names},
        "source_sha256": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in sources},
        "scanner_controls": "pass",
    }
    (ROOT / "audit/axioms.json").write_text(json.dumps(report, indent=2) + "\n")
    print("AXIOM_AND_SOURCE_AUDIT_PASS", len(records), "declarations", report["axioms"])


if __name__ == "__main__":
    main()
