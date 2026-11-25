"""Replay the P04 roots for the repository's checked-out revision using Nanoda."""
import argparse
import hashlib
import json
import re
import subprocess
import tempfile
from pathlib import Path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", required=True, type=Path, help="built P04 checkout")
    parser.add_argument("--lake", default="lake")
    parser.add_argument("--leanexport", default="leanexport")
    parser.add_argument("--nanoda", default="nanoda_bin")
    args = parser.parse_args()
    repo = args.repo.resolve()
    revision = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=repo, text=True
    ).strip()
    index = Path(__file__).with_name("p04_lean_replay.json")
    groups = json.loads(index.read_text(encoding="utf-8"))
    for group, archived in groups.items():
        if archived["revision"] == revision:
            break
    else:
        parser.error("checkout one of the two commits listed in the supplement")
    module, roots = archived["module"], archived["roots"]
    axioms = ["propext", "Classical.choice", "Quot.sound"]
    if archived["permitted_axioms"] != axioms:
        raise SystemExit("unexpected axiom list in the archived record")
    out = repo / ".lake" / "p04-replay" / group
    out.mkdir(parents=True, exist_ok=True)
    run_lake = [args.lake, "env"]
    with tempfile.TemporaryDirectory(dir=out) as tmp:
        directory = Path(tmp)
        export = directory / "proof.jsonl"
        with export.open("wb") as stream:
            subprocess.run(run_lake + [args.leanexport, module, "--", *roots],
                           stdout=stream, cwd=repo, check=True)
        with export.open("rb") as stream:
            digest = hashlib.file_digest(stream, "sha256").hexdigest()
        types = directory / "statements.txt"
        types.touch()
        config = directory / "nanoda.json"
        config.write_text(json.dumps({
            "export_file_path": str(export),
            "permitted_axioms": axioms,
            "unsafe_permit_all_axioms": False,
            "unpermitted_axiom_hard_error": True,
            "nat_extension": True,
            "string_extension": True,
            "pp_declars": roots,
            "pp_output_path": str(types),
            "pp_options": {"proofs": False},
            "print_success_message": True,
        }), encoding="utf-8")
        result = subprocess.run(run_lake + [args.nanoda, str(config)], cwd=repo,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                text=True, encoding="utf-8")
        print(result.stdout.rstrip(), flush=True)
        result.check_returncode()
        statements = types.read_text(encoding="utf-8")
        for root in roots:
            if not re.search(r"^theorem " + re.escape(root) + r"(?=\.\{|\s|:)", statements, re.M):
                raise SystemExit(f"missing exported theorem {root}")
        count = re.search(r"^Checked (\d+) declarations with no errors$", result.stdout, re.M)
        if not count:
            raise SystemExit("missing declaration count in the checker output")
        if int(count.group(1)) != archived["checked_declarations"]:
            raise SystemExit(f"unexpected declaration count {count.group(1)}")
        if digest != archived["export_sha256"]:
            raise SystemExit(f"export SHA-256 {digest} differs from the archived fingerprint")
        (out / "statements.txt").write_text(statements, encoding="utf-8")
        record = {"revision": revision, "module": module, "roots": roots,
                  "permitted_axioms": axioms, "export_sha256": digest,
                  "checked_declarations": int(count.group(1)), "nanoda": result.stdout.strip()}
        (out / "replay.json").write_text(json.dumps(record, indent=2) + "\n", encoding="utf-8")
        print(f"{digest}  {out / 'replay.json'}", flush=True)


if __name__ == "__main__":
    main()
