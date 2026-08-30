#!/usr/bin/env python3

import hashlib
import json
import os
from pathlib import Path
import sys
import tempfile


CANONICAL_PREFIX = "src/kernel/implementation/syscall_alloc_quota/"


def repo_root() -> Path:
    return Path(__file__).resolve().parents[2]


def read_event() -> dict:
    try:
        value = json.load(sys.stdin)
    except (json.JSONDecodeError, OSError):
        return {}
    return value if isinstance(value, dict) else {}


def file_hash(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as source:
        for chunk in iter(lambda: source.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def snapshot(root: Path) -> dict[str, str]:
    source_root = root / "src"
    if not source_root.is_dir():
        return {}
    result = {}
    for path in sorted(source_root.rglob("*.rs")):
        if path.is_file():
            result[path.relative_to(root).as_posix()] = file_hash(path)
    return result


def changed_paths(before: dict[str, str], after: dict[str, str]) -> list[str]:
    return sorted(
        path for path in before.keys() | after.keys()
        if before.get(path) != after.get(path)
    )


def state_dir(root: Path, session_id: str) -> Path:
    key = hashlib.sha256(session_id.encode("utf-8")).hexdigest()
    return root / ".codex" / ".style-gate" / key


def load_snapshot(path: Path) -> dict[str, str] | None:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (FileNotFoundError, json.JSONDecodeError, OSError):
        return None
    if not isinstance(value, dict):
        return None
    return {
        str(name): str(digest)
        for name, digest in value.items()
        if isinstance(name, str) and isinstance(digest, str)
    }


def write_snapshot(path: Path, value: dict[str, str]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f"{path.name}.{os.getpid()}.tmp")
    temporary.write_text(
        json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n",
        encoding="utf-8",
    )
    temporary.replace(path)


def emit(value: dict) -> None:
    print(json.dumps(value, separators=(",", ":")))


def session_start(event: dict) -> int:
    session_id = event.get("session_id")
    if not isinstance(session_id, str) or not session_id:
        emit({"continue": True})
        return 0

    root = repo_root()
    state = state_dir(root, session_id)
    certified = state / "certified.json"
    if not certified.exists():
        write_snapshot(certified, snapshot(root))
        (state / "pending.json").unlink(missing_ok=True)

    emit({
        "hookSpecificOutput": {
            "hookEventName": "SessionStart",
            "additionalContext": (
                "VeriFlat style gate is active. Before editing src/**/*.rs, "
                "read AGENTS.md and mirror the hand-edited "
                "src/kernel/implementation/syscall_alloc_quota/ directory. "
                "If this session changes Verus source, Stop will require a "
                "final style pass over the exact changed files."
            ),
        }
    })
    return 0


def stop(event: dict) -> int:
    session_id = event.get("session_id")
    if not isinstance(session_id, str) or not session_id:
        emit({"continue": True})
        return 0

    root = repo_root()
    state = state_dir(root, session_id)
    certified_path = state / "certified.json"
    pending_path = state / "pending.json"
    current = snapshot(root)
    certified = load_snapshot(certified_path)
    if certified is None:
        write_snapshot(certified_path, current)
        emit({"continue": True})
        return 0

    changed = changed_paths(certified, current)
    if not changed:
        pending_path.unlink(missing_ok=True)
        emit({"continue": True})
        return 0

    pending = load_snapshot(pending_path)
    if pending == current:
        write_snapshot(certified_path, current)
        pending_path.unlink(missing_ok=True)
        emit({"continue": True})
        return 0

    write_snapshot(pending_path, current)
    shown = changed[:40]
    file_list = "\n".join(f"- {path}" for path in shown)
    if len(changed) > len(shown):
        file_list += f"\n- ... and {len(changed) - len(shown)} more"
    canonical_changed = any(
        path.startswith(CANONICAL_PREFIX) for path in changed
    )
    canonical_warning = ""
    if canonical_changed:
        canonical_warning = (
            "\nThe canonical syscall_alloc_quota directory changed during "
            "this session. It is user-owned and must remain byte-identical; "
            "remove only this session's edits before finishing.\n"
        )

    reason = (
        "Run the required final VeriFlat style pass before finishing. Review "
        "the current forms of the files below against AGENTS.md and the "
        "hand-edited src/kernel/implementation/syscall_alloc_quota/ directory. "
        "Check compact spec/proof/exec contracts, one-line short assert-by "
        "blocks, no live mutable reference at invariant closure, scoped reveals, triggers, "
        "dead proof scaffolding, and EOF invariant-closure rules. Fix every "
        "finding and run the smallest relevant verification. If you edit code "
        "during that pass, Stop will request one final pass over the resulting "
        "content; if the content is already clean, finish again without "
        "changing it."
        f"{canonical_warning}\nSession-changed Verus files:\n{file_list}"
    )
    emit({"decision": "block", "reason": reason})
    return 0


def self_test() -> int:
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        source = root / "src" / "sample.rs"
        source.parent.mkdir(parents=True)
        source.write_text("fn one() {}\n", encoding="utf-8")
        first = snapshot(root)
        assert changed_paths(first, first) == []
        source.write_text("fn two() {}\n", encoding="utf-8")
        second = snapshot(root)
        assert changed_paths(first, second) == ["src/sample.rs"]
        source.unlink()
        assert changed_paths(second, snapshot(root)) == ["src/sample.rs"]
    print("style_gate self-test: ok")
    return 0


def main() -> int:
    if len(sys.argv) != 2:
        print("usage: style_gate.py session-start|stop|self-test", file=sys.stderr)
        return 2
    mode = sys.argv[1]
    if mode == "self-test":
        return self_test()
    event = read_event()
    if mode == "session-start":
        return session_start(event)
    if mode == "stop":
        return stop(event)
    print(f"unknown mode: {mode}", file=sys.stderr)
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
